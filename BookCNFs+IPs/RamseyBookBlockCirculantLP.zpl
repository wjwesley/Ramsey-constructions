#Integer program to determine whether there is a 2-block circluant construction to prove the lower bound R(B_r, B_q) > 2N. 

param N := 33; #modulus
param r := 16; 
param q := 17; 

set V := {0..N-1};
set Vplus := {1..N-1}; 

var x[<i> in V] binary;
var y[<i> in V] binary; 
var z[<i> in V] binary; 

var s[<i,d> in V*V] binary; # d \in D11 and i, i+d \in D11
var t[<i,d> in V*V] binary; # d \in D22 and i, i+d \in D22
var u1[<i,d> in V*V] binary;  # d \in D11 and i, i+d \in D12
var u2[<i,d> in V*V] binary;  # d \in D22 and i, i+d \in D12
var ubar1[<i,d> in V*V] binary; #d \in D11 and i, i+d \in \bar D12 
var ubar2[<i,d> in V*V] binary; #d \in D22 and i, i+d \in \bar D12 
var su[<i,d> in V*V] binary; # d \in D12 and i \in D12, d-i \in D11 
var ut[<i,d> in V*V] binary; # d \in D12 and i \in D22, i+d \in D12 
var tubar[<i,d> in V*V] binary; 
var ubars[<i,d> in V*V] binary; 
var ansatzS[<i,d> in V*V] binary; 

#subto ansatzPaley: x[1] + x[4]+x[9]+x[16]+x[25]+x[7]+x[20]+x[6]+x[23]+x[13]+x[5] == 11; 
#subto ansatzPaley37: x[1] + x[4]+x[9]+x[16]+x[25]+x[36]+x[12]+x[27]+x[7]+x[26]+x[10]+x[33]+x[21]+x[11]+x[3]+x[34]+x[30]+x[28] == 18; 
#subto ansatz: forall <i> in V: x[i] == z[i]; 
#subto ansatzD12symm: forall <i> in V: z[i] == z[-i mod N]; 
#subto ansatzPaley61: x[1]+x[4]+x[9]+x[16]+x[25]+x[36]+x[49]+x[3]+x[20]+x[39]+x[60]+x[22]+x[12]+x[13]+x[14] == 15;
#subto ansatz: x[1] + x[2] + x[3] + x[4] == 4; 
#subto ansatz2: z[1] + z[2] + z[3] + z[4] +z[6] +z[8] +z[9] + z[12] + z[13] + z[16] + z[18] == 0;
#subto ansatz3: x[1]+x[4]+x[9]+x[16]  == 4;
#subto ansatz4: z[0]+z[1]+z[2] +z[3] == 4;
#subto ansatz5: z[5]+z[6]+z[7] + z[8] + z[12]+z[13] == 0;  
#subto ansatzBalanceS: forall <d1,d2> in Vplus*Vplus : (sum <i> in V: ansatzS[i,d1]) - (sum <i> in V: ansatzS[i,d2]) <= 1; 

#subto ansatzd11DiffsAnd1 : forall <i,d> in V*V : ansatzS[i,d] <= x[i]; 
#subto ansatzd11DiffsAnd2 : forall <i,d> in V*V : ansatzS[i,d] <= x[(i+d) mod N]; 
#subto ansatzd11DiffsAnd3 : forall <i,d> in V*V : ansatzS[i,d] >= x[i] + x[(i+d) mod N] - 1;


subto diag1:  x[0] == 0; 
subto diag2:  y[0] == 0; 
subto symm1: forall <i> in V: x[i] == x[-i mod N]; 
subto symm2: forall <i> in V: y[i] == y[-i mod N]; 
subto comp: forall <i> in Vplus: x[i] == 1-y[i]; 


subto d11DiffsAnd1 : forall <i,d> in V*V : s[i,d] <= x[i]; 
subto d11DiffsAnd2 : forall <i,d> in V*V : s[i,d] <= x[(i+d) mod N]; 
subto d11DiffsAnd3 : forall <i,d> in V*V : s[i,d] >= x[i] + x[(i+d) mod N] + x[d] - 2;
subto d11DiffsAnd4 : forall <i,d> in V*V : s[i,d] <= x[d];  

subto d22DiffsAnd1 : forall <i,d> in V*V : t[i,d] <= y[i]; 
subto d22DiffsAnd2 : forall <i,d> in V*V : t[i,d] <= y[(i+d) mod N]; 
subto d22DiffsAnd3 : forall <i,d> in V*V : t[i,d] >= y[i] + y[(i+d) mod N] + y[d] -2;
subto d22DiffsAnd4 : forall <i,d> in V*V : t[i,d] <= y[d]; 

subto d12DiffsAnd1 : forall <i,d> in V*V : u1[i,d] <= z[i]; 
subto d12DiffsAnd2 : forall <i,d> in V*V : u1[i,d] <= z[(i+d) mod N]; 
subto d12DiffsAnd3 : forall <i,d> in V*V : u1[i,d] >= z[i] + z[(i+d) mod N] + x[d] - 2;
subto d12DiffsAnd4 : forall <i,d> in V*V : u1[i,d] <= x[d]; 

subto d12DiffsAnd5 : forall <i,d> in V*V : u2[i,d] <= z[i]; 
subto d12DiffsAnd6 : forall <i,d> in V*V : u2[i,d] <= z[(i+d) mod N]; 
subto d12DiffsAnd7 : forall <i,d> in V*V : u2[i,d] >= z[i] + z[(i+d) mod N] + y[d] - 2;
subto d12DiffsAnd8 : forall <i,d> in V*V : u2[i,d] <= y[d]; 

subto d11d12DiffsAnd1 : forall <i,d> in V*V : su[i,d] <= z[i]; 
subto d11d12DiffsAnd2 : forall <i,d> in V*V : su[i,d] <= x[(d-i) mod N]; 
subto d11d12DiffsAnd3 : forall <i,d> in V*V : su[i,d] >= z[i] + x[(d-i) mod N] +z[d]-2;
subto d11d12DiffsAnd4 : forall <i,d> in V*V : su[i,d] <= z[d];                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           


subto d12d22DiffsAnd1 : forall <i,d> in V*V : ut[i,d] <= y[i]; 
subto d12d22DiffsAnd2 : forall <i,d> in V*V : ut[i,d] <= z[(i+d) mod N]; 
subto d12d22DiffsAnd3 : forall <i,d> in V*V : ut[i,d] >= y[i] + z[(i+d) mod N] +z[d]-2;
subto d12d22DiffsAnd4 : forall <i,d> in V*V : ut[i,d] <= z[d]; 

subto d12BarDiffsAnd1 : forall <i,d> in V*V : ubar1[i,d] <= 1-z[i]; 
subto d12BarDiffsAnd2 : forall <i,d> in V*V : ubar1[i,d] <= 1-z[(i+d) mod N]; 
subto d12BarDiffsAnd3 : forall <i,d> in V*V : ubar1[i,d] >= 1-z[i] + 1-z[(i+d) mod N] +x[d] - 2;
subto d12BarDiffsAnd4 : forall <i,d> in V*V : ubar1[i,d] <= x[d]; 

subto d12BarDiffsAnd5 : forall <i,d> in V*V : ubar2[i,d] <= 1-z[i]; 
subto d12BarDiffsAnd6 : forall <i,d> in V*V : ubar2[i,d] <= 1-z[(i+d) mod N]; 
subto d12BarDiffsAnd7 : forall <i,d> in V*V : ubar2[i,d] >= 1-z[i] + 1-z[(i+d) mod N] +y[d] - 2;
subto d12BarDiffsAnd8 : forall <i,d> in V*V : ubar2[i,d] <= y[d]; 

subto d22d12barSumsAnd1 : forall <i,d> in V*V : tubar[i,d] <= 1-z[i]; 
subto d22d12barSumsAnd2 : forall <i,d> in V*V : tubar[i,d] <= y[(d-i) mod N]; 
subto d22d12barSumsAnd3 : forall <i,d> in V*V : tubar[i,d] >= 1-z[i] + y[(d-i) mod N] +1-z[d]-2;
subto d2d12barSumsAnd4: forall <i,d> in V*V : tubar[i,d] <= 1-z[d]; 

subto d12bard11DiffsAnd1 : forall <i,d> in V*V : ubars[i,d] <= x[i]; 
subto d12bard11DiffsAnd2 : forall <i,d> in V*V : ubars[i,d] <= 1-z[(i+d) mod N]; 
subto d12bard11DiffsAnd3 : forall <i,d> in V*V : ubars[i,d] >= x[i] + 1-z[(i+d) mod N] + 1-z[d] -2;
subto d12bard11DiffsAnd4: forall <i,d> in V*V : ubars[i,d] <= 1-z[d]; 

subto noBr1 : forall <d> in V: sum <i> in V : (s[i,d] + u1[i,d])<= r-1;
subto noBr2 : forall <d> in V: sum <i> in V : (t[i,d] + u2[i,d]) <= r-1;
subto noBr3 : forall <d> in V: sum <i> in V : (su[i,d] + ut[i,d]) <= r-1; 

#this is assuming that D11 and D22 are complements

subto noBs1 : forall <d> in V: sum <i> in V : (t[i,d] + ubar2[i,d]) <= q-1; 
subto noBs2 : forall <d> in V: sum <i> in V : (s[i,d] + ubar1[i,d]) <= q-1; 
subto noBs3 : forall <d> in V: sum <i> in V : (tubar[i,d] + ubars[i,d]) <= q-1; 

#subto tests : x[1]+x[3]+x[4]+x[5]+x[12]+x[13]+x[14]+x[16] == 8;
#subto tests2 : z[1]+z[3]+z[6]+z[8]+z[9]+z[12]+z[13]+z[15] >= 8; 