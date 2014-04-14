package main

import (
	"fmt"
	"os"
	"flag"
	"encoding/hex"
	"github.com/edsrzf/mmap-go"
	"github.com/larspensjo/config"
	"errors"
	"bytes"
	"encoding/json"
	"strings"
	"net"
	"time"
	"strconv"
	"hash/crc32"
	"hash/adler32"
)

const (
	MARK = uint32(4294967295)
)

type Counter interface {
	WriteItem() (int, error)
	ReadItem() (int, error)
	DeleteItem() (int, error)
	Inc() (int, error)
	Get() (string, error)
}

type User struct {
	mmap []byte
}

type Counts map[string] int

var (
	configFile     = flag.String("configfile", "./config.ini", "General configuration file")
	Config         = make(map[string]string)
	keyLength      = uint32(0)
	maxValueLength = uint32(0)
	itemMaxCount   = uint32(0)
	maxSearchDepth = uint32(0)
	emptyValue     = []byte{}
	emptyKey       = []byte{}
	deletedKey     = []byte{}
	fieldMap       = map[string] int{}
	valueMap       = map[int] string{}
	shortcutMap    = map[string] string{}
	user           = User{}
)

func CompressInt32Array(in []int32) (out []byte, error error) {
	inlength := len(in)
	if inlength == 0 {
		return out, errors.New("VariableByte/Compress: inlength = 0. No work done.")
	}
	buf := make([]byte, inlength*8)

	currentinpos := uint32(0)
	for _, v := range in[0: inlength] {
		val := uint32(v)
		for val >= 0x80 {

			buf[currentinpos] = (byte(val)|0x80)
			currentinpos ++
			val >>= 7
		}
		buf[currentinpos] = byte(val)
		currentinpos ++
	}
	for currentinpos%4 != 0 {
		buf[currentinpos] = 0x80
		currentinpos ++
	}

	if currentinpos < maxValueLength {
		buf[maxValueLength-1] = byte(currentinpos - 1)|0xf0
	}else if currentinpos == maxValueLength {
		//刚好16字节 不加length
	}else {
		//超过16字节 overflow
		fmt.Println("//超过16字节 overflow")
		return emptyValue, error
	}

	return buf[:maxValueLength], error
}

func UncompressByteArray(in []byte) (out []int32, error error) {
	inlength := len(in)
	if inlength == 0 {
		return make([]int32,len(fieldMap)), nil
	}
	buf := make([]int32, inlength*2)
	tmpoutpos := 0
	for p, v, move := 0, 0, uint(0); p < inlength; p++ {
		c := int(in[p])
		v = v+(c&127)<<(move*7)
		if c&128 == 0 {
			//正常情况
			buf[tmpoutpos] = int32(v)
			tmpoutpos++
			v, move = 0, 0
			continue
		}
		move++
	}
	return buf[:tmpoutpos], error
}

func RSHash(key []byte) uint32 {
	//hash算法1
	return crc32.ChecksumIEEE(key) & 0x7FFFFFFF
}

func DEKHash(key []byte) uint32 {
	//hash算法2
	return adler32.Checksum(key) & 0x7FFFFFFF
}

func GetExistMapFile(filename string) (file *os.File, error error) {
	_, err := os.Stat(filename)

	if err != nil && !os.IsExist(err) {
		return nil, errors.New("No file exists.")
	}
	//有文件打开文件
	file, err2 := os.OpenFile(filename, os.O_CREATE|os.O_APPEND|os.O_RDWR, os.FileMode(0660))
	if (err2 != nil) {
		return nil, errors.New("open file failed")
	}
        return file, nil
}

func CreateMapFile(filename string, size int) (file *os.File, error error) {
	//没有文件创建空文件
	new_file, err := os.Create(filename)
	if err != nil {
		return nil, errors.New("Create file error.")
	}
	new_file.Seek(int64(size - 1), 0)
	new_file.Write([]byte("\x00"))
	return new_file, nil
}

func IncByteKey(old_byte_key []byte, n uint32) uint32 {

	length := len(old_byte_key)
	bt := make([]byte, length)

	copy(bt, old_byte_key)

	if length < 2 {
		fmt.Println("key too short...")
		return 0
	}
	last := bt[length-2: length]
	b := uint32(last[0]) << 8 + uint32(last[1]) + n

	bt[length-2] = byte((int(b) >> 8) & 255)
	bt[length-1] = byte(int(b) & 255)
	return DEKHash(bt)
}

func (c User) FindItem(byte_key []byte, tp int) (uint32, error) {

	if len(byte_key) != 12 {
		return 1, errors.New("find item key length error")
	}
	offset := uint32(0)
	h1 := RSHash(byte_key)
	offset = h1 % uint32(itemMaxCount) * uint32((keyLength + maxValueLength))
	searched_key := c.mmap[offset: offset+keyLength]
	is_modify := bytes.Equal(searched_key, byte_key)
	is_empty := bytes.Equal(searched_key, emptyKey)
	hash_collisions_count := uint32(0)
	delete_offset := MARK

	if tp == 0 {
		//read model
		if is_modify || is_empty {
			//找到了
			return offset, nil
		}

		//第一次没找到key 并且找到的key不为空，循环查找下一个空key或者匹配key
		for hash_collisions_count < maxSearchDepth && !is_empty && !is_modify {
			hash_collisions_count++
			offset = ((h1+IncByteKey(byte_key, hash_collisions_count))%itemMaxCount)*(keyLength+maxValueLength)
			searched_key = c.mmap[offset: offset+keyLength]
			is_modify = bytes.Equal(searched_key, byte_key)
			is_empty = bytes.Equal(searched_key, emptyKey)
		}
//		fmt.Println("hash_collisions_count", hash_collisions_count)

		if hash_collisions_count < maxSearchDepth {
			return offset, nil
		}
		return MARK, errors.New("not find item for read")
	} else if tp == 1 {
		//write model
		if is_modify || is_empty {
			//找到了
			return offset, nil
		}
		is_delete := bytes.Equal(searched_key, deletedKey)

		if is_delete {
			//删除的key， 记住位置 继续查找
			delete_offset = offset
		}

		for hash_collisions_count < maxSearchDepth && !is_empty && !is_modify {
			hash_collisions_count++
			offset = ((h1 + IncByteKey(byte_key, hash_collisions_count)) % itemMaxCount) * (keyLength+maxValueLength)
//			fmt.Println(offset)
			searched_key = c.mmap[offset: offset+keyLength]
			is_modify = bytes.Equal(searched_key, byte_key)
			is_delete = bytes.Equal(searched_key, deletedKey)
			is_empty = bytes.Equal(searched_key, emptyKey)
			if is_delete && delete_offset == MARK {
				//删除的key， 记住第一次出现的位置 继续查找
				delete_offset = offset
			}
		}
		if is_modify || (is_empty && delete_offset == MARK ) {
			//找到了 或者是没有包含delete key的路径
			//空key 并且路径之中没有delete key
			return offset, nil
		}

		if is_empty && delete_offset != MARK || (delete_offset != MARK && hash_collisions_count >= maxSearchDepth) {
			//空key 并且路径之中有delete key
			return delete_offset, nil
		}
		fmt.Println("hash_collisions_count",hash_collisions_count)
		return MARK, errors.New("not find location for write")
	}
//	fmt.Println("find item argument error")

	return MARK, errors.New("find item argument error")
}

func (c User) WriteItem(key string, offset uint32, val []byte) (int, error) {
	if offset != MARK {
		byte_key, _ := hex.DecodeString(key)
		offset, err := c.FindItem(byte_key, 1)
		if err != nil {
			return -1, errors.New("cannot found")
		}
		copy(c.mmap[offset:], byte_key)
		copy(c.mmap[offset+keyLength:], val)

	}else {
		copy(c.mmap[offset+keyLength:], val)
	}
	return -1, nil
}

func (c User) ReadItem(key string) ([]int32, uint32, error) {

	byte_key, err := hex.DecodeString(key)
	offset, err := c.FindItem(byte_key, 0)
//	fmt.Println("find", offset, err)

	if err != nil {
		return nil, 0, errors.New("cannot found")
	}
	val_bytes := c.mmap[offset+keyLength:]
	if bytes.Equal(val_bytes, emptyValue) {
		//空的值
		return make([]int32, len(fieldMap)), offset, nil
	}

	cc := int(val_bytes[maxValueLength - 1])
	length := 0
	if cc>>4 == 15 {
		length = cc&15+1
	}

	val, err := UncompressByteArray(val_bytes[:length])
	if err != nil {
		return []int32{}, 0, errors.New("value error")
	}

	return val, offset, nil
}

func (c User) DeleteItem(key string) (int, error) {
	byte_key, err := hex.DecodeString(key)
	offset, err := c.FindItem(byte_key, 0)
	if err != nil {
		return 1, errors.New("cannot found")
	}
	copy(c.mmap[offset:], deletedKey)
	return 0, nil
}

func (c User) Inc(key string, field string, val int) (int, error) {
	index := fieldMap[field]
	int_array, offset, err := c.ReadItem(key)

	if err != nil {
		//没有找到
		int_array = make([]int32, len(fieldMap))
		return 0, nil
	}

	//有老数据
	int_array[index] += int32(val)

	data, err := CompressInt32Array(int_array)
	if err != nil {
		data = emptyValue
	}

//	fmt.Println("data", data)
	c.WriteItem(key, offset, data)
	return 0, nil
}

func (c User) Get(key string, empty_value bool) ([]byte, error) {
	int_array, offset, err := c.ReadItem(key)
	if err != nil{
		//没有找到
		int_array = make([]int32, len(fieldMap))
	}

	nc := make(Counts)
	total := 0
	for k, v := range int_array {
		if len(valueMap[k]) != 0 {
			nc[valueMap[k]] = int(v)
			total += int(v)
		}
	}
	nc["Total"] = total
	byte_array, err := json.Marshal(nc)
	if err != nil {
		return []byte{'{', '}'}, errors.New("error")
	}
	if empty_value {
		copy(c.mmap[offset+keyLength:], emptyValue)
	}
	return byte_array, nil
}

func handleClient(conn net.Conn) {
	conn.SetReadDeadline(time.Now().Add(2 * time.Minute)) // set 2 minutes timeout
	request := make([]byte, 128) // set maxium request length to 128KB to prevent flood attack
	defer conn.Close()  // close connection before exit
	for {read_len, err := conn.Read(request)
		if err != nil || read_len == 0 {
			//connection already closed by client
			break
		}
		r := strings.Split(string(request), "\r\n")
		if r[0] == "*4" && r[1] == "$7" && strings.ToUpper(r[2]) == "HINCRBY" && r[3] == "$24" {
			//inc
			uid := r[4]
			incrby, _ := strconv.Atoi(r[8])
			field := r[6]
			user.Inc(uid, shortcutMap[field], incrby)
			conn.Write([]byte("+OK\r\n"))
		} else if r[0] == "*2" && r[1] == "$3" && strings.ToUpper(r[2]) == "GET" && r[3] == "$24" {
			//get
			uid := r[4]
			j, _ := user.Get(uid, false)
			return_string := "$" + strconv.Itoa(len(j)) + "\r\n" + string(j) + "\r\n"
			//			user.DeleteItem(uid)
			conn.Write([]byte(return_string))
		}else if r[0] == "*2" && r[1] == "$3" && strings.ToUpper(r[2]) == "DEL" && r[3] == "$24" {
			//delete
			uid := r[4]
			user.Get(uid, true)
//			return_string := "$" + strconv.Itoa(len(j)) + "\r\n" + string(j) + "\r\n"
			//			user.DeleteItem(uid)
//			conn.Write([]byte(return_string))
			conn.Write([]byte("+1\r\n"))
		} else {
			conn.Write([]byte("+OK\r\n"))
		}
		request = make([]byte, 128) // clear last read content
	}
}

func checkError(err error) {
	if err != nil {
		fmt.Fprintf(os.Stderr, "Fatal error: %s", err.Error())
		os.Exit(1)
	}
}

func initConfig() {
	flag.Parse()
	//set config file std
	cfg, err := config.ReadDefault(*configFile)
	if err != nil {
		fmt.Println("Fail to find", *configFile, err)
	}
	//set config file std End

	//Initialized topic from the configuration
	if cfg.HasSection("Settings") {
		section, err := cfg.SectionOptions("Settings")
		if err == nil {
			for _, v := range section {
				options, err := cfg.String("Settings", v)
				if err == nil {
					Config[v] = options
				}
			}
		}
	}

	t1, _ := strconv.Atoi(Config["max_search_depth"])
	maxSearchDepth = uint32(t1)
	t2, _ := strconv.Atoi(Config["key_length"])
	keyLength = uint32(t2)
	t3, _ := strconv.Atoi(Config["max_value_length"])
	maxValueLength = uint32(t3)
	t4, _ := strconv.Atoi(Config["item_max_count"])
	itemMaxCount = uint32(t4)


	emptyKey = make([]byte, keyLength)
	emptyValue = make([]byte, maxValueLength)
	deletedKey = make([]byte, keyLength)
	shortcutArray := strings.Split(Config["fields_shortcut"], ",")
	fields := strings.Split(Config["fields"], ",")


	for k, v := range fields {
		fieldMap[v] = k
		valueMap[k] = v
		shortcutMap[shortcutArray[k]] = v
	}

	for i := 0; i < int(keyLength); i++ {
		deletedKey[i] = byte(255)
	}

//	fmt.Println("gaga",keyLength, maxValueLength, int(itemMaxCount*(keyLength+maxValueLength)))
	map_file, err := GetExistMapFile(Config["filename"])
	if err != nil {
		map_file, _ = CreateMapFile(Config["filename"], int(itemMaxCount*(keyLength+maxValueLength)))
	}
	defer map_file.Close()
	mmap, _ := mmap.Map(map_file, mmap.RDWR, 0)

	user = User{mmap}
}

func main() {
	initConfig()
	service := ":1200"
	fmt.Println("starting in", service)
	tcpAddr, err := net.ResolveTCPAddr("tcp4", service)
	checkError(err)
	listener, err := net.ListenTCP("tcp", tcpAddr)
	checkError(err)
	for {
		conn, err := listener.Accept()
		if err != nil {
			continue
		}
		go handleClient(conn)
	}
}

