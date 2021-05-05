#List of  packages required
#PySimpleGui
#pycryptodome


import PySimpleGUI as sg
import math
import numpy as np
import random
from Crypto.Cipher import AES
from base64 import b64encode, b64decode
import csv 
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib
matplotlib.use("TkAgg")


# DEFINE FUNCTIONS --------------------------------------------------------------------------------------------------------------------------------------------

#Calculate modular inverse
def modInverse(a, p):
    modInv = pow(a, -1, p)
    
    return modInv

#Calculate Q+P - Following addition algorithm
def addition(x1, y1, x2, y2):

    #If initial point is point at infinity, then resulting point is point 
    #at infinity
    if x1 == 0 and y1 == 0 or (y1==0 and y2 == 0):                                                     
        R_x = x2
        R_y = y2
    #If new point is point at infinity, then result is original point
    #i.e. (n-1)P = 0 => nP = P + (n-1)P = P + 0 = P    
    elif x2 == 0 and y2 == 0:                                                   
        R_x = x1
        R_y = y1
    #If P1 = - P2, then result is point at infinity
    elif x1 == x2 and (y1 != y2):                                               
        R_x = 0
        R_y = 0
    #Addition algo for same points
    elif x1==x2 and y1==y2:                                                     
        slope = ((3 * (x1**2) + a) * modInverse(2*y1, p)) % p
        R_x = (slope**2 - x1 - x2) % p
        R_y = (slope*(x1 - R_x) - y1) % p
    #Addition algo for different points
    else:                                                                       
        slope = ((y2 - y1) * modInverse(x2 - x1, p)) % p 
        R_x = (slope**2 - x1 - x2) % p
        R_y = (slope*(x1 - R_x) - y1) % p

    #check
    RHS = ((R_x**3) + (a*R_x) + b) % p
    LHS = ((R_y)**2) % p 
    #Ensures that generated point is either on the curve 
    #(by checking equation is true), or point at infinity
    if RHS != LHS and (R_x != 0 and R_y != 0):                                  
        print("Calculation: (",x2,y2,")+(",x1,y1,") = ", R_x, R_y)
        raise Warning("Generated point does not lay on curve")
            
    return R_x, R_y

#Calculate nP - Following addition algorithm
def multiplication(x1, y1, n):
    #Set "old point" to initial point
    x2 = x1                                                                     
    y2 = y1

    #Cases for 1*P and 0*P (Shouldnt have these cases but just incase)
    if n == 0:                                                                  
        R_x = 0
        R_y = 0
    elif n == 1:
        R_x = x1
        R_y = y1
    else:
        for j in range(2, n + 1):
            #If initial point is point at infinity, 
            #then resulting point is point at infinity
            if (x1 == 0 and y1 == 0) or (y1 == 0 and y2 == 0):                                             
                R_x = 0
                R_y = 0
            #If P1 = - P2, then result is point at infinity
            elif x1 == x2 and (y1 != y2):                                       
                R_x = 0
                R_y = 0
            #If new point is point at infinity, then result is original 
            #point, i.e. (n-1)P = 0 => nP = P + (n-1)P = P + 0 = P
            elif x2 == 0 and y2 == 0:                                           
                R_x = x1
                R_y = y1
            #Addition algo for same points
            elif x1==x2 and y1==y2:                                            
                slope = ((3 * (x1**2) + a) * modInverse(2*y1, p)) % p
                R_x = (slope**2 - x1 - x2) % p
                R_y = (slope*(x1 - R_x) - y1) % p
            #Addition algo for different points
            else:                                                               
                slope = ((y2 - y1) * modInverse(x2 - x1, p)) % p 
                R_x = (slope**2 - x1 - x2) % p
                R_y = (slope*(x1 - R_x) - y1) % p

            #check each time
            RHS = ((R_x**3) + (a*R_x) + b) % p
            LHS = ((R_y)**2) % p
            
            #Ensures that generated point is either on the curve 
            #(by checking equation is true), or point at infinity
            if RHS != LHS and (R_x != 0 and R_y != 0):                          
                print("Points with issue: (", R_x, R_y, ")", j,"times....", RHS, "=/=", LHS)
                print("Calculation: (",x2,y2,")*(",x1,y1,") = ", R_x, R_y)
                raise Warning("Generated point does not lay on curve")

            #Set old point to new derived point
            x2 = R_x                                                            
            y2 = R_y              
    return R_x, R_y

def doubleAndAdd(x1, y1, n):
    Q_x = x1
    Q_y = y1
    R_x = 0
    R_y = 0
    
    while n > 0:
        if n % 2 == 1:
            R_x, R_y = addition(R_x, R_y, Q_x, Q_y)
            
        Q_x, Q_y = multiplication(Q_x, Q_y, 2)
        n = math.floor(n/2)
        print(n)
            
    return R_x, R_y
            
#Tonelli shanks to solve y^2 = n mod p for use in "find_y"
#Define Legendre symbol (n^ (p-1)/2). Non zero quadratic residue 
#only exists for LS == 1
def legendreSymbol(n, p):                                                       
    if (p - 1) % 2 == 0:
        LS = pow(n, (p - 1) // 2, p)
    else:
        sg.Popup("Prime Issue!", "P is not an odd prime!")
    
    return LS
 
def tonelliShanks(n, p):
    if legendreSymbol(n,p) == 1:
        if n % p == 0:
            r = 0
        
        #If p = 3 mod 4, then r = +- n^((p+1)/4) mod p
        if p % 4 == 3:                                                          
           r = pow(n, (p+1)//4, p) 
        
        #Want p-1 = q*(2^s), q odd, so beign with 1 = p-1 and s  = 0 and 
        #continue to factor out multiples of 2 until q is odd
        q = p-1                                                                 
        s = 0
        
        while q % 2 == 0:
            q //= 2
            s += 1
         
        #Want Z to be non quadratic residue, i.e legendre != 1
        z = 2                                                                  
         
        while legendreSymbol(z, p) == 1:
             z += 1
             
        m = s
        c = pow(z, q, p)
        t = pow (n, q, p)
        r = pow(n, ((q+1)//2), p) 
         
        while t != 1:           
             i = 0
             j = t
             
             #Find least i such that t^(2^i) = 1 
             while j != 1:      
                 i += 1
                 j = pow(j, 2, p)
                 
             powb = 2 ** (m - i - 1) 
                 
             b = pow(c, powb, p)
             m = i
             c = pow(b, 2, p)
             t = (t * pow(b,2)) % p
             r = (r * b) % p
                 

        #1 solution at r, the other at p-r
        print("Y values = ", r, p-r)
        return r, p-r                                                           
             
    else:
        sg.Popup("X-Coordinate Issue!","Cannot find Y value for given x-coordinate!")
        print(legendreSymbol(n,p))
    return r

#Derive y value given x value (used to generate pub key point)
def find_y(singlePubKey):
    pubKey_x = int(str(singlePubKey)[1:])
    parity = int(str(singlePubKey)[0])
    eqnSolution = ((pubKey_x**3) + (a*pubKey_x) + b) % p

    y1_temp = None

    y1_temp, y2_temp = tonelliShanks(eqnSolution, p)

    if y1_temp != None:
        #Check if y value should be odd or even and assign actual y value to y 1 or y2
        if (parity == 1 and y1_temp % 2 == 0) or (parity == 2 and y1_temp % 2 != 0):   
            final_y = y1_temp
        elif (parity == 1 and y2_temp % 2 == 0) or (parity == 2 and y2_temp % 2 != 0):
            final_y = y2_temp
    elif y1_temp == None:
        sg.Popup("Key Issue!", "Their Public Key is not valid!")

    return final_y

#AES Encryption
def AES_Encrypt(shared_coord):
    #This creates the cipher from the symmetric key (Using EAX method), 
    #which for ECC will be the shared coordinate generated by both parties
    cipher = AES.new(shared_coord, AES.MODE_EAX)

    #Generates "nonce" every time which is essentially random number used in 
    #AES to stop replay attacks. Neceessary to create to use pycrptodome AES                                       
    nonce = cipher.nonce   
       
    #This is where the message is encoded into the cipher text                                                      
    cipherText_temp, tag = cipher.encrypt_and_digest(plainText_input.encode("utf-8") )  

    #Decoding Cipher text so it doesnt display as bytes for display reasons, 
    #will be re-encoded to bites during decryption
    cipherText = b64encode(cipherText_temp).decode()   

    #Turning nonce into an integer for display reasons, 
    #as it will be copied by the user when decoding                                 
    nonce_decode = int.from_bytes(nonce, byteorder="big")                               
    
    print("Cipher Text: ", cipherText)
    print("Nonce: ", nonce_decode)

    return cipherText, nonce_decode

#AES Decryption
def AES_Decrypt(shared_coord, cipherText, nonce):

    #Takes the integer nonce, and encodes it into bytes to be used below
    nonce_temp = nonce.to_bytes(16, byteorder="big")                            
    cipherText_temp = b64decode(cipherText)

    cipher = AES.new(shared_coord, AES.MODE_EAX, nonce=nonce_temp)    

    #This is where the cipher text is decrypted back into the plain text      
    plainText = cipher.decrypt(cipherText_temp)                                 

    #Decode the plain text so it doesnt display as a byte string 
    #i.e. b"This is the string"
    print("Plain Text: ", plainText.decode("latin-1"))                          
    print()

    return plainText

#GUI SETUP ---------------------------------------------------------------------------------------------------------------------------------------------------

#Options Screen
layout_style =   [[sg.Text("Key Exchange Method: ", size=(20,1)), sg.InputCombo(("Diffie-Hellman", "ECIES"), default_value="Diffie-Hellman", size=(20, 1), readonly=True, enable_events=True, key="INPUT-KEY-EXCHANGE"),],
                  [sg.Text("a = ", size=(20,1)), sg.In(size=(39, 1), enable_events=True, key="INPUT-A"),],
                  [sg.Text("b = ", size=(20,1)), sg.In(size=(39, 1), enable_events=True, key="INPUT-B"),],
                  [sg.Text("p = ", size=(20,1)), sg.In(size=(39, 1), enable_events=True, key="INPUT-P"),],
                  [sg.Text("x = ", size=(20,1)), sg.In(size=(39, 1), default_text="0", enable_events=True, key="INPUT-X"),],
                  [sg.Text("y = ", size=(20,1)), sg.In(size=(39, 1), default_text="0", enable_events=True, key="INPUT-Y"),],
                  [sg.Text("Save Location:", size=(20,1)), sg.In(size=(25, 1), enable_events=True, key="SAVE-LOCATION"), sg.FolderBrowse(),],
                  [sg.Text("Save Name:", size=(20,1)), sg.In(size=(20, 1), enable_events=True, key="SAVE-FILE-NAME"), sg.Button("Save (CSV)", size=(10, 1), enable_events=True, key="SAVE-SELECTION"),],
                  [sg.Text("Import from File:", size=(20,1)), sg.In(size=(25, 1), enable_events=True, key="OPEN-FILE"), sg.FileBrowse(file_types=(("CSV Files", "*.csv"),),),],
                  [sg.Text(" ", size=(20,1)), sg.Button("Import", size=(10, 1), enable_events=True, key="IMPORT-FILE", disabled=True),],
                  [sg.Text("Generate Starting Point: ", size=(20,1)), sg.Button("Generate",     size=(20, 1), enable_events=True, key="GENERATE-START"),],
                  
                  [sg.Text("_"  * 63),],
                  
                  [sg.Text("Input Message:", size=(20,1)), sg.Multiline(default_text="Paste your plain text into here and click Encrypt...", size=(35, 4), enable_events=True, key="INPUT-PLAINTEXT"),],
                  [sg.Text("Cipher Text:", size=(20,1)),   sg.Multiline(default_text="Paste your cipher text into here and click Encrypt...", size=(35, 4), enable_events=True, key="INPUT-CIPHERTEXT")],
                  [sg.Text("Their Public Key:", size=(20,1)), sg.Multiline(size=(35, 3), enable_events=True, key="R-PUBLIC-KEY"),],
                  [sg.Text("My Public Key:", size=(20,1)), sg.Multiline(size=(35, 3), enable_events=True, key="S-PUBLIC-KEY")],
                  [sg.Text("My Private Key:", size=(20,1)), sg.Multiline(size=(35, 3), enable_events=True, key="S-PRIVATE-KEY")],
                  [sg.Text("Generate Key Pair:", size=(20,1)), sg.Button("Generate",     size=(20, 1), enable_events=True, key="GENERATE-KEY-PAIR"),],
                  [sg.Text("Nonce (Decryption Only):", size=(20,1)),    sg.Multiline(default_text="", size=(35, 3), enable_events=True, key="INPUT-NONCE")],
                  [sg.Text("R (ECIES Decryption Only):", size=(20,1)),      sg.Multiline(default_text="", size=(35, 3), enable_events=True, key="INPUT-R")],
                  
                  [sg.Text("_"  * 63),],
                  
                  [sg.Button("Encrypt",    size=(20, 1), enable_events=True, key="START_ENCRYPT"),
                   sg.Button("Decrypt",     size=(20, 1), enable_events=True, key="START_DECRYPT"),],
                  [sg.Button("Brute Force (p<1000)", size=(20, 1), enable_events=True, key="BRUTE-FORCE"), 
                   sg.Button("Pohlig Rho Attack", size=(20, 1), enable_events=True, key="RHO-ATTACK")],

                  [sg.Text("_"  * 63),],
                  
                  [sg.Button("Exit",        size=(20, 1), enable_events=True, key="EXIT"),],]

#REDUNDANT BUT KEEPING INCASE SOMETHING GOES WRONG SO I CAN COPY --------------------------------------------------------------------------------------------------------------------------------
text_screen =    [[sg.Text("Input Message:"), sg.Multiline(default_text="Paste your plain text into here and click Encrypt...", size=(35, 4), enable_events=True, key="INPUT-PLAINTEXT"),],
                  [sg.Text("Cipher Text:     "),   sg.Multiline(default_text="Paste your cipher text into here and click Encrypt...", size=(35, 4), enable_events=True, key="INPUT-CIPHERTEXT")],
                  [sg.Button("Encrypt",    size=(20, 1), enable_events=True, key="START_ENCRYPT"),
                   sg.Button("Decrypt",     size=(20, 1), enable_events=True, key="START_DECRYPT"),],
                  [sg.Text("_"  * 51),],
                  [sg.Button("Brute Force (p<1000)", size=(20, 1), enable_events=True, key="BRUTE-FORCE"), 
                   sg.Button("MOV Attack", size=(20, 1), enable_events=True, key="MOV-ATTACK")],]

attack_screen =  [[sg.Text("Their Public Key:               "), sg.Multiline(size=(35, 3), enable_events=True, key="R-PUBLIC-KEY"),],
                  [sg.Text("My Public Key:                  "), sg.Multiline(size=(35, 3), enable_events=True, key="S-PUBLIC-KEY")],
                  [sg.Text("My Private Key:                 "), sg.Multiline(size=(35, 3), enable_events=True, key="S-PRIVATE-KEY")],
                  [sg.Text("Generate Key Pair:             "), sg.Button("Generate",     size=(20, 1), enable_events=True, key="GENERATE-KEY-PAIR"),],
                  [sg.Text("Nonce (Decryption Only):    "),    sg.Multiline(default_text="", size=(35, 3), enable_events=True, key="INPUT-NONCE")],
                  [sg.Text("R (ECIES Decryption Only):"),      sg.Multiline(default_text="", size=(35, 3), enable_events=True, key="INPUT-R")],
                  [sg.Button("Exit",        size=(20, 1), enable_events=True, key="EXIT"),],]
#------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

canvas_screen =  [[sg.Canvas(key="CANVAS")], [sg.Text("Generate Finite Field Graph:"), sg.Button("Generate", size=(20, 1), enable_events=True, key="GENERATE-GRAPH")],
                  [sg.Text("P_x = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-P-X"), sg.Text("Q_x = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-Q-X"), sg.Text("R_x = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-R-X", disabled=True), sg.Button("Suggest Points", size=(20, 1), enable_events=True, key="SUGGEST-POINTS"),],
                  [sg.Text("P_y = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-P-Y"), sg.Text("Q_y = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-Q-Y"), sg.Text("R_y = "), sg.In(size=(5, 1), enable_events=True, key="INPUT-R-Y", disabled=True), sg.Button("Add Points", size=(20, 1), enable_events=True, key="START-ADDITION"),],]


layout = [[sg.Column(layout_style), sg.VSeperator(), sg.Column(canvas_screen)]]

#ACTUAL GUI -----------------------------------------------------------------------------------------------------------------------------------------------------
# Create the window
window = sg.Window(title="ECC Project", layout=layout, finalize=True)

#Flag and prebuilt figure for gui for GUI
genuineStartFlag = 0                                                            
genuineIntFlag = 0

#Setup matplotlib graph
figure = matplotlib.figure.Figure(figsize=(8.5, 8.5), dpi=100)

xValues = [0] 
yValues = [0]

ax1 = figure.add_subplot(111)

ax1.plot(yValues, xValues, "")
ax1.set_xlim([0,100])
ax1.set_ylim([0,100])
minor_ticks = np.arange(0, 100, 1)
           
ax1.set_xticks(minor_ticks, minor=True)
ax1.set_yticks(minor_ticks, minor=True)
ax1.grid(which='minor', alpha=0.2)
ax1.grid(which='major', alpha=0.5)

figure.subplots_adjust(0.05,0.05,0.97,0.97)

canvas = FigureCanvasTkAgg(figure, window["CANVAS"].TKCanvas,)
canvas.get_tk_widget().pack(side="top", fill="both", expand=1)

# Create event loop
while True:
    event, values = window.read()
    # End program on EXIT click or window close
    if event in ("EXIT", sg.WIN_CLOSED):
        break

    #Set to assign values when trying to encrypt, decrypt or generate key pair
    if event in ("START_ENCRYPT", 
                 "START_DECRYPT", 
                 "GENERATE-KEY-PAIR", 
                 "GENERATE-GRAPH", 
                 "GENERATE-START", 
                 "BRUTE-FORCE", 
                 "START-ADDITION", 
                 "SUGGEST-POINTS"):        
        genuineStartFlag = 0
        genuineIntFlag = 0

        #Check params are all whole numbers, unless generate start in which case only check a,b,p
        if ((event not in ("GENERATE-START", "START-ADDITION", "SUGGEST-POINTS") and 
            bool(values["INPUT-A"].strip("-").isnumeric()) == True and 
            bool(values["INPUT-B"].strip("-").isnumeric) == True and 
            bool(values["INPUT-P"].strip().isnumeric) == True and 
            bool(values["INPUT-X"].strip().isnumeric) == True and 
            bool(values["INPUT-Y"].strip().isnumeric) == True) or 
            (event in ("GENERATE-START", "START-ADDITION", "SUGGEST-POINTS") and 
             bool(values["INPUT-A"].strip("-").isnumeric()) == True and 
             bool(values["INPUT-B"].strip("-").isnumeric) == True and 
             bool(values["INPUT-P"].strip().isnumeric) == True)):       

            #Set parameters to input box values
            temp_a = int(values["INPUT-A"])                                     
            temp_b = int(values["INPUT-B"])
            temp_p = int(values["INPUT-P"])
            
            #Only set starting point if we're not generating it
            if event not in ("GENERATE-START", "START-ADDITION", "SUGGEST-POINTS"):  
                temp_P_x = int(values["INPUT-X"])
                temp_P_y = int(values["INPUT-Y"])       

            #Assign Values based on input boxes
            #Write message
            plainText_input = values["INPUT-PLAINTEXT"]
            cipherText_input = values["INPUT-CIPHERTEXT"]

            #Define key exchange method: DH=Diffie Hellman ; ECIES = ECIES
            exchangeType=values["INPUT-KEY-EXCHANGE"]

            #Define curve and prime field: [y^2 = x^3 + ax + b in E(F_p)]
            a = temp_a
            b = temp_b
            p = temp_p

            #Flag to show all params are integers
            genuineIntFlag = 1                                                  
            
            #Only checks genuine start if not generating. 
            #2 if statments so temp py and px dont casue crash when python cant find them.
            if event not in ("GENERATE-START", "START-ADDITION", "SUGGEST-POINTS"):   
                #Check that starting point is genuine                                    
                if ((temp_P_y)**2) % temp_p == (temp_P_x**3 + (temp_a * temp_P_x) + temp_b) % temp_p: 
                    #Pre determined starting point on curve
                    P_x = temp_P_x
                    P_y = temp_P_y
                    
                    #Flag to show starting point is genuine
                    genuineStartFlag = 1                                            
    
                elif (((temp_P_y)**2) % temp_p != (temp_P_x**3 + (temp_a * temp_P_x) + temp_b) % temp_p and 
                      event != "GENERATE-START"):
                    sg.Popup("Parameter Error!", "Starting Point is not genuine!")
            
            #Check discriminant = 0
            if 4*(temp_a**3) + 27*(temp_b**2) != 0:                             
                discrimFlag = 1
            else:
                sg.Popup("Discriminant Error!", "4a^3 + 27b^2 must not equal 0!")

        else:
            sg.Popup("Parameter Error!", "Not all parameters are integers!")

    #DISABLE SELECTIONS BASED ON CERTAIN PARAMETERS -------------------------------------------------------------------------------------------------------------
    #Disable Import unless path is populated 
    if values["OPEN-FILE"] == "":
        #Disables Import button if no path to folder
        window.FindElement("IMPORT-FILE").Update(disabled=True)                 
    elif values["OPEN-FILE"] != "":
        window.FindElement("IMPORT-FILE").Update(disabled=False)
        

    #STARTING POINT GENERATION ----------------------------------------------------------------------------------------------------------------------------------
    #Find starting point
    if (event == "GENERATE-START" and 
        genuineIntFlag == 1 and 
        discrimFlag == 1):
        
        #Reset starting point flag
        foundPoint = 0         
        
        #Reset x and y, x takes random value < p/2 so we can have a random starting point                                                 
        x = random.randint(0, math.floor(p/2))                                  
        y = 1

        #Define curve and prime field: [y^2 = x^3 + ax + b in E(F_p)]
        a = int(values["INPUT-A"]) 
        b = int(values["INPUT-B"])
        p = int(values["INPUT-P"])

        #Find starting point x value
        while foundPoint < 1 :  
            #RHS of ECC eqn                                                
            eqnSolutionMod = ((x**3) + (a*x) + b) % p                           

            #Find starting point y value 
            while foundPoint < 1 and y < p:  
                #Check if Y is a square mod p                                   
                if bool(eqnSolutionMod == y**2 % p) == True:                    

                    #Assign 2 points to be used in Graph update
                    genStart_x = x                                              
                    genStart_y = y

                    #Update gui textbox
                    window.Element("INPUT-X").Update(str(x))                    
                    window.Element("INPUT-Y").Update(str(y))
                    
                    #Break both loops
                    foundPoint = 1                                              
                    print("Found point:",x,y)
                
                y += 1
            
            y = 0
            x += 1
            
            #If doesnt find starting point, start again (possible if randint()
            #selects integer after highest possible x value)
            if x == p:                                                          
               x = random.randint(0, p) 

        genuineStartFlag == 1

    #KEY GENERATION ---------------------------------------------------------------------------------------------------------------------------------------------
    if (event == "GENERATE-KEY-PAIR" and 
        genuineIntFlag == 1 and 
        genuineStartFlag == 1 and 
        discrimFlag == 1):
        
        #Priv key is random number < #E(F)
        sendPriv = random.randint(2, math.floor(p + 1 - (2*(p**(1/2))))) 
        
        #Pub key consists of 2 points
        sendPub_Point = doubleAndAdd(P_x, P_y, sendPriv)                   

        #Compress public key (point) into 1 string as the x-value, and 1 byte 
        #at the start stating if it is the odd or even y value (1=even, 2=odd)
        if sendPub_Point[1] % 2 == 0:                                           
            sendPub = int("1" + str(sendPub_Point[0]))
        elif sendPub_Point[1] % 2 != 0:
            sendPub = int("2" + str(sendPub_Point[0]))
        else:
           raise Warning("Bad y value")

        window.Element("S-PUBLIC-KEY").Update(str(sendPub))
        window.Element("S-PRIVATE-KEY").Update(str(sendPriv))

    # ENCRYPTION =------------------------------------------------------------------------------------------------------------------------------------------------
    #Check for encrypt button click
    if (event == "START_ENCRYPT" and 
        genuineIntFlag == 1 and 
        genuineStartFlag == 1 and 
        discrimFlag == 1):    
        
        #Check All keys are whole numbers.              
        if (bool((values["S-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["S-PRIVATE-KEY"].strip()).isdecimal()) == True and 
            bool((values["R-PUBLIC-KEY"].strip()).isdecimal()) == True): 
            
            #Assign Key variables values
            sendPub = int(values["S-PUBLIC-KEY"])                               
            sendPriv = int(values["S-PRIVATE-KEY"])
            recPub = int(values["R-PUBLIC-KEY"])

            #Check keys match starting point
            theoreticalPub = doubleAndAdd(int(P_x), int(P_y), int(sendPriv))[0]
            actualPub = int(str(sendPub)[1:])

            if theoreticalPub == actualPub:
                if exchangeType == "Diffie-Hellman":
                    #Diffie-Hellman Encryption
                    #Multiply public key point to itself a number of times 
                    #equal to the private key to get shared coordinate
                    SharedCoord_int = doubleAndAdd(int(str(recPub)[1:]), find_y(recPub), sendPriv)[0]  
                    #Convert shared coord to bytes for use in AES (required)
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")                                                    

                    #Generates cipher text and nonce to be sent to other person
                    cipherText, nonce = AES_Encrypt(SharedCoord_byte)                                       
                    cipherText_output = str(cipherText)

                    window.Element("INPUT-CIPHERTEXT").Update(str(cipherText_output))
                    window.Element("INPUT-NONCE").Update(str(nonce))

                    saveFlag = 1

                    print("Encryption Pub Key:", sendPub)
                    print("Encryption Priv:", sendPriv)
                    print("Decrypt Pub:", recPub)
                    print("Encryption Shared Coord:", SharedCoord_int)
                    print("Nonce:",nonce)

                elif exchangeType == "ECIES":
                    #ECIES Encryption
                    #Generate random number < #E(F)
                    randNum = random.randint(2, math.floor(p + 1 - (2*(p**(1/2)))))    
                    
                    #Multiply the starting point by the random number                      
                    R_Point = doubleAndAdd(P_x, P_y, randNum)                                              
    
                    #Use same method as key generation to turn R point into 
                    #single integer for key
                    if R_Point[1] % 2 == 0:                                                                  
                        R = int("1" + str(R_Point[0]))
                    elif R_Point[1] % 2 != 0:
                        R = int("2" + str(R_Point[0]))
                    else:
                        raise Warning("Bad y value")

                    #Shared coord is public key times random number
                    SharedCoord_int = doubleAndAdd(int(str(recPub)[1:]), find_y(recPub), randNum)[0]
                    
                    #Convert shared coord to bytes for use in AES (required)
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")                                    

                    #Generates cipher text and nonce to be sent to other person
                    cipherText, nonce = AES_Encrypt(SharedCoord_byte)                                        

                    cipherText_output = str(cipherText)

                    window.Element("INPUT-CIPHERTEXT").Update(str(cipherText_output))
                    window.Element("INPUT-NONCE").Update(str(nonce))
                    window.Element("INPUT-R").Update(str(R))

            else:
                sg.Popup("Starting Point/Key Mismatch!", 
                         "Your public and private keys do not match for this starting point!")
        else:
            sg.Popup("Key Error!", "Not all keys are integers!")


    #DECRYPTION =------------------------------------------------------------------------------------------------------------------------------------------------
    #Check for decrypt button click
    if (event == "START_DECRYPT" and 
        genuineIntFlag == 1 and 
        genuineStartFlag == 1 and 
        discrimFlag == 1): 
        
        #Check all keys and nonce are whole numbers.                                                   
        if (bool((values["S-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["S-PRIVATE-KEY"].strip()).isdecimal()) == True and 
            bool((values["R-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["INPUT-NONCE"].strip()).isdecimal()) == True): 
            
            #Check keys match starting point
            #Assign Key variables values [Sender, Receiver, nonce, ciphertext]  
            sendPub = int(values["S-PUBLIC-KEY"])                                                                        
            recPub = int(values["R-PUBLIC-KEY"])           
            sendPriv = int(values["S-PRIVATE-KEY"])
            theoreticalPub = doubleAndAdd(int(P_x), int(P_y), int(sendPriv))[0]
            actualPub = int(str(sendPub)[1:])

            if theoreticalPub == actualPub:
                nonce = int(values["INPUT-NONCE"])      
                cipherText = values["INPUT-CIPHERTEXT"].encode("utf-8")
                print(cipherText)

                if exchangeType == "Diffie-Hellman":
                    #Diffie-Hellman Decryption
                    #Repeat as encryption
                    SharedCoord_int = doubleAndAdd(int(str(recPub)[1:]), find_y(recPub), sendPriv)[0]        
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")               

                    #Decrpts using shared coord and text
                    plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)                               
                    plainText_output = plainText.decode("latin-1")
                    print(plainText_output)

                    window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))

                    print("Decryption Pub Key:", sendPub)
                    print("Decryption Priv:", sendPriv)
                    print("Encrypt Pub:", recPub)
                    print("Decryption Shared Coord:", SharedCoord_int)
                    print("Nonce:",nonce)
                    print()

                elif exchangeType == "ECIES" and bool((values["INPUT-R"].strip()).isdecimal()) == True:
                    #ECIES Decryption
                    R = int(values["INPUT-R"])

                    #Derive shared coord as R*privKey 
                    #(decryptPriv*R = decryptPriv*r*G = r*(decryptPriv*G) = r*decryptPub = S
                    SharedCoord_int = doubleAndAdd(int(str(R)[1:]), find_y(R), sendPriv)[0]                   
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")

                    plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)  
                    plainText_output = plainText.decode("latin-1")
                    print(plainText_output)

                    window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))

                elif exchangeType == "ECIES" and bool(values["INPUT-R"].isdecimal()) == False:
                    sg.Popup("R Error!", "The R value is not an integer!")
            else:
                sg.Popup("Starting Point/Key Mismatch!", 
                         "Your public and private keys do not match for this starting point!")
        else:
            sg.Popup("Key Error!", "Either the keys or nonce are not all integers!")

    #BRUTE FORCE =------------------------------------------------------------------------------------------------------------------------------------------------
    #Check for brute force button click
    if (event == "BRUTE-FORCE" and 
        genuineIntFlag == 1 and 
        genuineStartFlag == 1 and 
        discrimFlag == 1): 
        
        #Check all public keys and nonce are legitimate                                                                                            
        if (bool((values["S-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["R-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["INPUT-NONCE"].strip()).isdecimal()) == True):

            #Recievers Pub key input read from "My public key" section
            sendPub = int(values["S-PUBLIC-KEY"])

            #Derive Receivers Pub key coords
            pubKey_x = int(str(sendPub)[1:])                                    
            pubKey_y = find_y(sendPub)
            
            #Reset current force attempts coords
            current_x = 0                                                       
            current_y = 0

            print("Starting Point:")
            print("Public Key x coord:", pubKey_x)
            print("Public Key y coord:", pubKey_y)
            
            #Check all values of nP for n < prime and  when not matching
            for i in range(2, math.floor(p + 1 - (2*(p**(1/2))))):             
                current_x, current_y = doubleAndAdd(P_x, P_y, i)
                print("For n = ", i, ", nP = ",current_x, current_y)
                
                #Set Final public key to xcoord plus 1/2 if even/odd
                if (pubKey_x == current_x and pubKey_y == current_y):           
                    forced_privKey = i
                    break
            
            print("Guessed Private Key:", forced_privKey)
            
            #Assign Key variables values [Sender, Receiver, nonce]
            sendPub = int(values["S-PUBLIC-KEY"])                               
            sendPriv = forced_privKey
            
            window.Element("S-PRIVATE-KEY").Update(str(forced_privKey))

            recPub = int(values["R-PUBLIC-KEY"])
            nonce = int(values["INPUT-NONCE"])      
            cipherText = values["INPUT-CIPHERTEXT"].encode("utf-8")
            print(cipherText)

            if exchangeType == "Diffie-Hellman":
                #Diffie-Hellman Decryption
                #Repeat as encryption
                SharedCoord_int = doubleAndAdd(int(str(recPub)[1:]), find_y(recPub), sendPriv)[0]        
                SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")               
                
                #Decrpts using shared coord and text
                plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)                               
                plainText_output = plainText.decode("latin-1")
                print(plainText_output)

                window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))

                print("Decryption Pub Key:", sendPub)
                print("Decryption Priv:", sendPriv)
                print("Encrypt Pub:", recPub)
                print("Decryption Shared Coord:", SharedCoord_int)
                print("Nonce:",nonce)
                print()

            elif exchangeType == "ECIES" and bool((values["INPUT-R"].strip()).isdecimal()) == True:
                #ECIES Decryption
                R = int(values["INPUT-R"])
                
                #Derive shared coord as R*privKey 
                #(decryptPriv*R = decryptPriv*r*G = r*(decryptPriv*G) = r*decryptPub = S
                SharedCoord_int = doubleAndAdd(int(str(R)[1:]), find_y(R), sendPriv)[0]                   
                SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")

                plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)  
                plainText_output = plainText.decode("latin-1")
                print(plainText_output)

                window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))

    #POLLARDS RHO--------------------------------------------------------------
    #Check for pollards rho button click
    if (event == "RHO-ATTACK" and 
        genuineIntFlag == 1 and 
        genuineStartFlag == 1 and 
        discrimFlag == 1):
        
        #count of total iterations to kill if taking too long
        totCount = 0
        maxAllowed = math.ceil(20*(p)^(1/2))
        
        #Check all public keys and nonce are legitimate                                                                                            
        if (bool((values["S-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["R-PUBLIC-KEY"].strip()).isdecimal()) == True and 
            bool((values["INPUT-NONCE"].strip()).isdecimal()) == True):
            
            #Read Starting Point
            P_x = int(values["INPUT-X"])
            P_y = int(values["INPUT-Y"])

            #Recievers Pub key input read from "My public key" section
            sendPub = int(values["S-PUBLIC-KEY"])

            #Derive Receivers Pub key coords
            pubKey_x = int(str(sendPub)[1:])                                    
            pubKey_y = find_y(sendPub)
            
            
            #Find order of Curve (k)
            #Collect all points into arays anc count length (NAIVE)
            x = 0 #Reset x and y1                                                   
            y = 0
            
            #Arrays to add values to 
            xValues = [0]                                                   
            yValues = [0]
            
            #Loop thorugh all possible X values
            while x < p :
                #RHS of ECC eqn                                                           
                eqnSolutionMod = ((x**3) + (a*x) + b) % p   
            
                #Loop through all y values                        
                while y < p/2:                              
                    #Check if Y is a square mod p                        
                    if bool(eqnSolutionMod == y**2 % p) == True:     
                        #Collate all x,y values
                        xValues.append(x)                                   
                        yValues.append(y)
                        if y != 0:
                            #Collct x twice for y > p/2
                            xValues.append(x)                                   
                            yValues.append(p-y)
                    y += 1
                y = 0
                x+=1
            
            #assign k
            if len(xValues) == len(yValues):
                k = len(xValues)
                print("k = ", k)
            else:
                sg.Popup("Can't determine curve order!")
            
            #Initialise ai, bi, aj, bj so gcd(bj - bi, k) != 1
            R1_a = 5 
            R1_b = 5 
            
            R2_a = R1_a
            R2_b = R1_b 
            
            #If unable to finds match such that gcd != 1, 
            #restart with new variables
            while math.gcd(R2_b - R1_b, k) != 1: 
                
                if totCount > maxAllowed:
                    sg.Popup("Took too long to find Key!")
                    break
                
                #randomly generate coefficients (ai, bi) = (aj, bj)
                R1_a = random.randint(1, k-1) 
                R1_b = random.randint(1, k-1) 
                
                R2_a = R1_a
                R2_b = R1_b   
                
                #Initial point R0 = a0 P + b0 Q
                R1_x, R1_y = addition(multiplication(P_x, P_y, R1_a)[0], 
                                multiplication(P_x, P_y, R1_a)[1], 
                                multiplication(pubKey_x, pubKey_y, R1_b)[0], 
                                multiplication(pubKey_x, pubKey_y, R1_b)[1] )
                
                R2_x, R2_y = addition(multiplication(P_x, P_y, R2_a)[0], 
                                multiplication(P_x, P_y, R2_a)[1], 
                                multiplication(pubKey_x, pubKey_y, R2_b)[0], 
                                multiplication(pubKey_x, pubKey_y, R2_b)[1] )
                
                print("R1 = ", R1_x, R1_y)
                print("ai = ", R1_a, "   bi = ", R1_b)
                print("")
                
                print("R2 = ", R2_x, R2_y)
                print("aj = ", R2_a, "   bj = ", R2_b)
                print("")
                
                #initialise counting variables
                iCount = 0
                jCount = 0
               
                #Runs while Ri != Rj, 
                #except for first few runs because Ri = Rj to start
                while iCount < 2 or not (R1_x == R2_x and R1_y == R2_y ):      
                    
                    #R(i+1) = Ri + P if Ri in group 1
                    if 0 <= R1_x < p/3:
                        R1_x, R1_y = addition(R1_x, R1_y, P_x, P_y)
                        R1_a = (R1_a + 1) % k
                        R1_b = (R1_b)
                    #R(i+1) = 2 Ri if Ri in group 2
                    elif p/3 <= R1_x <= (2*p)/3:
                        R1_x, R1_y = multiplication(R1_x, R1_y, 2)
                        R1_a = (2*R1_a) % k
                        R1_b = (2*R1_b) % k
                    #R(i+1) = Ri + Q if Ri in group 3
                    elif (2*p)/3 <= R1_x < p:
                        R1_x, R1_y = addition(R1_x, R1_y, pubKey_x, pubKey_y)
                        R1_a = (R1_a)
                        R1_b = (R1_b + 1) % k
                        
                    iCount += 1
                    totCount += 1
                    
                    #Same as above but loops twice, as Rj = R(2i)
                    for i in range(1, 3):
                        if 0 <= R2_x < p/3:
                            R2_x, R2_y = addition(R2_x, R2_y, P_x, P_y)
                            R2_a = (R2_a + 1) % k
                            R2_b = (R2_b)
                        elif p/3 <= R2_x <= (2*p)/3:
                            R2_x, R2_y = multiplication(R2_x, R2_y, 2)
                            R2_a = (2*R2_a) % k
                            R2_b = (2*R2_b) % k
                        elif (2*p)/3 <= R2_x < p:
                            R2_x, R2_y = addition(R2_x, R2_y, pubKey_x, pubKey_y)
                            R2_a = (R2_a)
                            R2_b = (R2_b + 1) % k
                            
                        jCount += 1
                            

                    
                    #debug        
                    print("i = ", iCount, "j = ", jCount) 
                    print ("")
                    
                    print("R1 = ", R1_x, R1_y)
                    print("ai = ", R1_a, "   bi = ", R1_b)
                    print("")
                    
                    print("R2 = ", R2_x, R2_y)
                    print("aj = ", R2_a, "   bj = ", R2_b)
                    print("")
                    print("gcd = ", math.gcd(R2_b - R1_b, k)) 
                    print("")
                    print("-----------------------------")                      
                
            if totCount < maxAllowed:
            
                print("R1 = ", R1_x, R1_y)    
                print("R2 = ", R2_x, R2_y)    
                    
                print("gcd = ", math.gcd(R2_b - R1_b, k)) 
                
                #Derive forced private key
                forced_privKey = ((R1_a - R2_a)* modInverse(R2_b - R1_b, k)) % k
                window.Element("S-PRIVATE-KEY").Update(str(forced_privKey))
                     
                print("Private Key = ", forced_privKey)
                
                #Assign Key variables values [Sender, Receiver, nonce]
                sendPub = int(values["S-PUBLIC-KEY"])                               
                sendPriv = forced_privKey
    
                recPub = int(values["R-PUBLIC-KEY"])
                nonce = int(values["INPUT-NONCE"])      
                cipherText = values["INPUT-CIPHERTEXT"].encode("utf-8")
                print(cipherText)
    
                if exchangeType == "Diffie-Hellman":
                    #Diffie-Hellman Decryption
                    #Repeat as encryption
                    SharedCoord_int = doubleAndAdd(int(str(recPub)[1:]), find_y(recPub), sendPriv)[0]        
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")               
                    
                    #Decrpts using shared coord and text
                    plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)                               
                    plainText_output = plainText.decode("latin-1")
                    print(plainText_output)
    
                    window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))
    
                    print("Decryption Pub Key:", sendPub)
                    print("Decryption Priv:", sendPriv)
                    print("Encrypt Pub:", recPub)
                    print("Decryption Shared Coord:", SharedCoord_int)
                    print("Nonce:",nonce)
                    print()
    
                elif exchangeType == "ECIES" and bool((values["INPUT-R"].strip()).isdecimal()) == True:
                    #ECIES Decryption
                    R = int(values["INPUT-R"])
                    
                    #Derive shared coord as R*privKey 
                    #(decryptPriv*R = decryptPriv*r*G = r*(decryptPriv*G) = r*decryptPub = S
                    SharedCoord_int = doubleAndAdd(int(str(R)[1:]), find_y(R), sendPriv)[0]                   
                    SharedCoord_byte = SharedCoord_int.to_bytes(16,"big")
    
                    plainText = AES_Decrypt(SharedCoord_byte, cipherText, nonce)  
                    plainText_output = plainText.decode("latin-1")
                    print(plainText_output)
    
                    window.Element("INPUT-PLAINTEXT").Update(str(plainText_output))
    #SAVE FILE -----------------------------------------------------------------------------------------------------------------------------------------------------------
    if event == "SAVE-SELECTION":
        if values["SAVE-LOCATION"].strip() != "":
            with open(values["SAVE-LOCATION"]+ "/" + values["SAVE-FILE-NAME"]+".csv", 'w', newline='') as csvfile:
                fieldnames = ["Key Exchange", "a", "b", "p", "x", "y", 
                              "sPubKey", "rPubKey", "nonce", "R", "Cipher Text"]
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    
                writer.writeheader()
    
                writer.writerow({"Key Exchange" : values["INPUT-KEY-EXCHANGE"], 
                                    "a": values["INPUT-A"], 
                                    "b": values["INPUT-B"], 
                                    "p": values["INPUT-P"], 
                                    "x": values["INPUT-X"], 
                                    "y": values["INPUT-Y"],
                                    "sPubKey": values["S-PUBLIC-KEY"],
                                    "rPubKey": values["R-PUBLIC-KEY"],
                                    "nonce": values["INPUT-NONCE"],
                                    "R": values["INPUT-R"],
                                    "Cipher Text": values["INPUT-CIPHERTEXT"]})
        else:
            sg.Popup("File Location Issue!", "Your File Location is Empty!")

    #READ FILE -----------------------------------------------------------------------------------------------------------------------------------------------------------
    if event == "IMPORT-FILE":
        with open(values["OPEN-FILE"]) as csvfile:
            fieldnames = ["Key Exchange", "a", "b", "p", "x", "y", 
                          "sPubKey", "rPubKey", "nonce", "R", "Cipher Text"]
            reader = csv.DictReader(csvfile, delimiter=',', fieldnames = fieldnames)

            for row in reader:
                window.Element("INPUT-KEY-EXCHANGE").Update(str(row["Key Exchange"]))
                window.Element("INPUT-A").Update(str(row["a"]))
                window.Element("INPUT-B").Update(str(row["b"]))
                window.Element("INPUT-P").Update(str(row["p"]))
                window.Element("INPUT-X").Update(str(row["x"]))
                window.Element("INPUT-Y").Update(str(row["y"]))
                window.Element("R-PUBLIC-KEY").Update(str(row["sPubKey"]))
                window.Element("S-PUBLIC-KEY").Update(str(row["rPubKey"]))
                window.Element("S-PRIVATE-KEY").Update(str(""))
                window.Element("INPUT-NONCE").Update(str(row["nonce"]))
                window.Element("INPUT-R").Update(str(row["R"]))
                window.Element("INPUT-CIPHERTEXT").Update(str(row["Cipher Text"]))
                
    #ADD POINTS -----------------------------------------------------------------------------------------------------------------------------------------------------------
    if event == "START-ADDITION" and genuineIntFlag == 1:
        #Check points lay on curve
        P_x = int(values["INPUT-P-X"])
        P_y = int(values["INPUT-P-Y"])
        Q_x = int(values["INPUT-Q-X"])
        Q_y = int(values["INPUT-Q-Y"])
        
        additionFlag = 0
        
        if (((P_x**3) + (a*P_x) + b) % p != ((P_y)**2) % p) and (P_x != 0 and P_y != 0):
            sg.Popup("P Point Issue!", "Point P does not lay on the curve!")
        elif (((Q_x**3) + (a*Q_x) + b) % p != ((Q_y)**2) % p) and (Q_x != 0 and Q_y != 0):
            sg.Popup("Q Point Issue!", "Point Q does not lay on the curve!")
        else:         
            #Only perform addition if point lays on curve
            R_x, R_y = addition(P_x, P_y, Q_x, Q_y)                             
                    
            window.Element("INPUT-R-X").Update(str(R_x))                        
            window.Element("INPUT-R-Y").Update(str(R_y))
            
            #Assigned for later
            add_P_x = P_x                                                           
            add_P_y = P_y            
            add_Q_x = Q_x            
            add_Q_y = Q_y            
            add_R_x = R_x            
            add_R_y = R_y
            
            additionFlag = 1
            
    #SUGGEST POINTS-----------------------------------------------------------------------------------------------------------------------------------------------------
    if event == "SUGGEST-POINTS" and genuineIntFlag == 1:
        
        #Collect all points into arays
        x = 0 #Reset x and y1                                                   
        y = 0
        
        #Arrays to add values to 
        suggest_xValues = [0]                                                   
        suggest_yValues = [0]
        
        #Loop thorugh all possible X values
        while x < p :
            #RHS of ECC eqn                                                           
            eqnSolutionMod = ((x**3) + (a*x) + b) % p   

            #Loop through all y values                        
            while y < p/2:                              
                #Check if Y is a square mod p                        
                if bool(eqnSolutionMod == y**2 % p) == True:     
                    #Collate all x,y values
                    suggest_xValues.append(x)                                   
                    suggest_yValues.append(y)
                    if y != 0:
                        #Collct x twice for y > p/2
                        suggest_xValues.append(x)                                   
                        suggest_yValues.append(p-y)
                y += 1
            y = 0
            x += 1
            
        #Select random x,y value from array and make P
        rand1 = random.randint(0, len(suggest_xValues) - 1)                         
        suggest_P_x = suggest_xValues[rand1]
        suggest_P_y = suggest_yValues[rand1]   
        
        #Select random x,y value from array and make Q
        rand2 = random.randint(0, len(suggest_xValues) - 1)                         
        suggest_Q_x = suggest_xValues[rand2]
        suggest_Q_y = suggest_yValues[rand2]

        #Update selection boxes
        window.Element("INPUT-P-X").Update(str(suggest_P_x))                    
        window.Element("INPUT-P-Y").Update(str(suggest_P_y))
        
        window.Element("INPUT-Q-X").Update(str(suggest_Q_x))
        window.Element("INPUT-Q-Y").Update(str(suggest_Q_y))
        
    #Generate Graph -----------------------------------------------------------------------------------------------------------------------------------------------------------
    if ((event in ("START_ENCRYPT", "START_DECRYPT", "GENERATE-GRAPH", "GENERATE-START") or 
         (event == "START-ADDITION" and additionFlag == 1 and p < 100))  and 
        genuineIntFlag == 1 and discrimFlag == 1 and p < 10000): 
        #Reset x and y
        x = 0 
        y = 0
        
        #Arrays to add values to
        xValues = [0]                                                            
        yValues = [0]
        
        #Loop thorugh all possible X values
        while x < p :                 
            #RHS of ECC eqn                                          
            eqnSolutionMod = ((x**3) + (a*x) + b) % p             
            #Loop through all y values              
            while y < p/2:                                              
                #Check if Y is a square mod p       
                if bool(eqnSolutionMod == y**2 % p) == True:              
                    #Collate all x,y values      
                    xValues.append(x)                                           
                    yValues.append(y)
                    if y != 0:
                        #Collect x twice for y > p/2, only take 1 value for 
                        #y = 0 (i.e. dont also take y = p value)
                        xValues.append(x)                                           
                        yValues.append(p-y)
                y += 1
            y = 0
            x += 1 
            
        #Clear figure and set it up for new graph
        figure.clear()                                                          
        ax1 = figure.add_subplot(111)
        ax1.plot(xValues, yValues, "bo")

        if event == "GENERATE-START":
            P_x = genStart_x
            P_y = genStart_y
            ax1.plot(P_x, P_y, "ro", markeredgecolor="k")
            
        elif genuineStartFlag == 1:
            P_x = int(values["INPUT-X"])
            P_y = int(values["INPUT-Y"])
            ax1.plot(P_x, P_y, "ro", markeredgecolor="k")
        
        #Assign values to all points to be added
        elif event == "START-ADDITION" and additionFlag == 1:
            P_x = int(add_P_x)                                                  
            P_y = int(add_P_y)
            Q_x = int(add_Q_x)
            Q_y = int(add_Q_y)
            R_x = int(add_R_x)
            R_y = int(add_R_y)
            
            #Set x to be linespace so can be used in line equation
            x_axis = np.linspace(0, p, 100)                                     
                           
            if (not (P_x == 0 and P_y == 0) and  #P not infinity
                not (Q_x == 0 and Q_y == 0) and  #Q not infinity 
                not (P_x == Q_x and P_y != Q_y ) and  #not same x coord but different points
                not (P_y == Q_y and P_x != Q_x) and     #not same y coord but different points 
                not (P_y == Q_y and P_x == Q_x and P_y == 0)): #Same point at y = 0
                #P = Q
                if (P_x == Q_x and P_y == Q_y) and (P_y != 0):                                       
                    m = ((3 * (P_x**2) + a) * modInverse(2*P_y, p)) % p
                    print("1: m = ", m)
                #P =/= Q
                elif (P_x != Q_x) and (P_y != Q_y):                                 
                    m = ((Q_y - P_y) * modInverse(Q_x - P_x, p)) % p  
                    print("2: m = ", m)
                    
                c = (P_y - (m*P_x)) % p 
                print("c = ", c)
                
                #Plots straight line connecting P and Q, shifted by +-(p/m) m + 1 times
                for i in range (0, math.ceil(abs(m)) + 1):                       
                    ax1.plot(x_axis, m*(x_axis - (i*(p/m))) + c, "-r")

                    ax1.plot(x_axis, m*(x_axis + (i*(p/m))) + c, "-r")
                    #p/m shift because when y = 0, x = -c/m; 
                    #y = p, x = (p - c)/m = (p/m - c/m) from y = mx + c]
                    #therefore when next line begins at y = 0, it must have 
                    #x = (p/m - c/m) which is previous x + p/m => 
                    #y = (x - p/m)*m + c  
            
            #If P is inverse Q                                                                      
            elif ((P_x == Q_x and P_y != Q_y) or 
                  (P_y == Q_y and P_x == Q_x and P_y == 0)):                                   
                ax1.axvline(x = Q_x, color ="r") 
                
            #If P at infinity plot vertical line at Q           
            elif (P_x == 0 and P_y == 0):                                        
                ax1.axvline(x = Q_x, color ="r")
                
            #If Q at infinity plot vertical line at P
            elif (Q_x == 0 and Q_y == 0):                                        
                ax1.axvline(x = P_x, color ="r") 
                
            #If P and Q lay on same horizontal line
            elif (P_x != Q_x and P_y == Q_y):                                   
                ax1.axhline(y=P_y, color="r")
                
            #If both at infinity, beg for mercy
            elif (P_x == 0 and P_y == 0) and (Q_x == 0 and Q_y == 0):                
                sg.Popup("Please dont!", 
                         "Please dont try and add both points at infinity!")
                
            #Plots 3 points (P,Q,R) over the top of scatter, with colours 
            #red, red and, green respectively.    
            ax1.plot(P_x, P_y, "ro", 
                     Q_x, Q_y, "ro", 
                     R_x, R_y, "go", 
                     R_x, p - R_y, "bo", 
                     markeredgecolor="k") 
            
            #Plots dashed line between R and -R 
            #(where P + Q intersects - R, and equals R)
            ax1.plot([R_x, R_x], [R_y, p - R_y], "b--")                                                                                                                
                                                                            
        ax1.set_xlim([0,p])
        ax1.set_ylim([0,p])
        
        if p < 100:
            minor_ticks = np.arange(0, p, 1)
           
            ax1.set_xticks(minor_ticks, minor=True)
            ax1.set_yticks(minor_ticks, minor=True)
            
        ax1.grid(which='minor', alpha=0.2)
        ax1.grid(which='major', alpha=0.5)
        
        canvas.get_tk_widget().forget()
        canvas = FigureCanvasTkAgg(figure, window["CANVAS"].TKCanvas)
        canvas.get_tk_widget().pack(side="top", fill="both", expand=1)
        canvas.draw()
        
    #Large Prime Warnings-----------------------------------------------------------------------------------------------------------------------------------------------------------------
    if event=="GENERATE-GRAPH" and p >= 1000:
        sg.Popup("Computing Power!", 
                 "Sorry! Graphing only works for primes smaller than 1000")
    elif event=="START-ADDITION" and p >= 100:
        sg.Popup("Visual Space!", 
                 "Note: Addition graphing is only available primes smaller than 100")


window.close()