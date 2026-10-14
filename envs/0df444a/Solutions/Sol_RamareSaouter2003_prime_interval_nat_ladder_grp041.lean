-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T14:36:13.858961+00:00
-- url     : https://prove2.me/submissions/a2b709e6-9424-4655-91d3-cd263554569c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02050

theorem solution (n : Nat)
    (hn : 1254452690677 < n) (hupper : n <= 1424081223991) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1336593334243 n with h2 | h2
  · -- n > 1336593334243
    rcases Nat.lt_or_ge 1377899383801 n with h4 | h4
    · -- n > 1377899383801
      rcases Nat.lt_or_ge 1399026013393 n with h6 | h6
      · -- n > 1399026013393
        rcases Nat.lt_or_ge 1409709822761 n with h8 | h8
        · -- n > 1409709822761
          rcases Nat.lt_or_ge 1416877401791 n with h10 | h10
          · -- n > 1416877401791
            rcases Nat.lt_or_ge 1420474771117 n with h12 | h12
            · -- n > 1420474771117
              exact RamareSaouter2003.prime_interval_nat_ladder_c02050 n (by omega) (by omega)
            · -- n <= 1420474771117
              exact RamareSaouter2003.prime_interval_nat_ladder_c02049 n (by omega) (by omega)
          · -- n <= 1416877401791
            rcases Nat.lt_or_ge 1413289093313 n with h12 | h12
            · -- n > 1413289093313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02048 n (by omega) (by omega)
            · -- n <= 1413289093313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02047 n (by omega) (by omega)
        · -- n <= 1409709822761
          rcases Nat.lt_or_ge 1402578305347 n with h10 | h10
          · -- n > 1402578305347
            rcases Nat.lt_or_ge 1406139567631 n with h12 | h12
            · -- n > 1406139567631
              exact RamareSaouter2003.prime_interval_nat_ladder_c02046 n (by omega) (by omega)
            · -- n <= 1406139567631
              exact RamareSaouter2003.prime_interval_nat_ladder_c02045 n (by omega) (by omega)
          · -- n <= 1402578305347
            exact RamareSaouter2003.prime_interval_nat_ladder_c02044 n (by omega) (by omega)
      · -- n <= 1399026013393
        rcases Nat.lt_or_ge 1388422734943 n with h8 | h8
        · -- n > 1388422734943
          rcases Nat.lt_or_ge 1391948250587 n with h10 | h10
          · -- n > 1391948250587
            rcases Nat.lt_or_ge 1395482669311 n with h12 | h12
            · -- n > 1395482669311
              exact RamareSaouter2003.prime_interval_nat_ladder_c02043 n (by omega) (by omega)
            · -- n <= 1395482669311
              exact RamareSaouter2003.prime_interval_nat_ladder_c02042 n (by omega) (by omega)
          · -- n <= 1391948250587
            exact RamareSaouter2003.prime_interval_nat_ladder_c02041 n (by omega) (by omega)
        · -- n <= 1388422734943
          rcases Nat.lt_or_ge 1381398323741 n with h10 | h10
          · -- n > 1381398323741
            rcases Nat.lt_or_ge 1384906100111 n with h12 | h12
            · -- n > 1384906100111
              exact RamareSaouter2003.prime_interval_nat_ladder_c02040 n (by omega) (by omega)
            · -- n <= 1384906100111
              exact RamareSaouter2003.prime_interval_nat_ladder_c02039 n (by omega) (by omega)
          · -- n <= 1381398323741
            exact RamareSaouter2003.prime_interval_nat_ladder_c02038 n (by omega) (by omega)
    · -- n <= 1377899383801
      rcases Nat.lt_or_ge 1357090070719 n with h6 | h6
      · -- n > 1357090070719
        rcases Nat.lt_or_ge 1367455360627 n with h8 | h8
        · -- n > 1367455360627
          rcases Nat.lt_or_ge 1370927924227 n with h10 | h10
          · -- n > 1370927924227
            rcases Nat.lt_or_ge 1374409257937 n with h12 | h12
            · -- n > 1374409257937
              exact RamareSaouter2003.prime_interval_nat_ladder_c02037 n (by omega) (by omega)
            · -- n <= 1374409257937
              exact RamareSaouter2003.prime_interval_nat_ladder_c02036 n (by omega) (by omega)
          · -- n <= 1370927924227
            exact RamareSaouter2003.prime_interval_nat_ladder_c02035 n (by omega) (by omega)
        · -- n <= 1367455360627
          rcases Nat.lt_or_ge 1360536455731 n with h10 | h10
          · -- n > 1360536455731
            rcases Nat.lt_or_ge 1363991545109 n with h12 | h12
            · -- n > 1363991545109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02034 n (by omega) (by omega)
            · -- n <= 1363991545109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02033 n (by omega) (by omega)
          · -- n <= 1360536455731
            exact RamareSaouter2003.prime_interval_nat_ladder_c02032 n (by omega) (by omega)
      · -- n <= 1357090070719
        rcases Nat.lt_or_ge 1346802924007 n with h8 | h8
        · -- n > 1346802924007
          rcases Nat.lt_or_ge 1350223326649 n with h10 | h10
          · -- n > 1350223326649
            rcases Nat.lt_or_ge 1353652368247 n with h12 | h12
            · -- n > 1353652368247
              exact RamareSaouter2003.prime_interval_nat_ladder_c02031 n (by omega) (by omega)
            · -- n <= 1353652368247
              exact RamareSaouter2003.prime_interval_nat_ladder_c02030 n (by omega) (by omega)
          · -- n <= 1350223326649
            exact RamareSaouter2003.prime_interval_nat_ladder_c02029 n (by omega) (by omega)
        · -- n <= 1346802924007
          rcases Nat.lt_or_ge 1339987949371 n with h10 | h10
          · -- n > 1339987949371
            rcases Nat.lt_or_ge 1343391138757 n with h12 | h12
            · -- n > 1343391138757
              exact RamareSaouter2003.prime_interval_nat_ladder_c02028 n (by omega) (by omega)
            · -- n <= 1343391138757
              exact RamareSaouter2003.prime_interval_nat_ladder_c02027 n (by omega) (by omega)
          · -- n <= 1339987949371
            exact RamareSaouter2003.prime_interval_nat_ladder_c02026 n (by omega) (by omega)
  · -- n <= 1336593334243
    rcases Nat.lt_or_ge 1293233896243 n with h4 | h4
    · -- n > 1293233896243
      rcases Nat.lt_or_ge 1313069310923 n with h6 | h6
      · -- n > 1313069310923
        rcases Nat.lt_or_ge 1323100187891 n with h8 | h8
        · -- n > 1323100187891
          rcases Nat.lt_or_ge 1329829741013 n with h10 | h10
          · -- n > 1329829741013
            rcases Nat.lt_or_ge 1333207271947 n with h12 | h12
            · -- n > 1333207271947
              exact RamareSaouter2003.prime_interval_nat_ladder_c02025 n (by omega) (by omega)
            · -- n <= 1333207271947
              exact RamareSaouter2003.prime_interval_nat_ladder_c02024 n (by omega) (by omega)
          · -- n <= 1329829741013
            rcases Nat.lt_or_ge 1326460720153 n with h12 | h12
            · -- n > 1326460720153
              exact RamareSaouter2003.prime_interval_nat_ladder_c02023 n (by omega) (by omega)
            · -- n <= 1326460720153
              exact RamareSaouter2003.prime_interval_nat_ladder_c02022 n (by omega) (by omega)
        · -- n <= 1323100187891
          rcases Nat.lt_or_ge 1316404504501 n with h10 | h10
          · -- n > 1316404504501
            rcases Nat.lt_or_ge 1319748123139 n with h12 | h12
            · -- n > 1319748123139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02021 n (by omega) (by omega)
            · -- n <= 1319748123139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02020 n (by omega) (by omega)
          · -- n <= 1316404504501
            exact RamareSaouter2003.prime_interval_nat_ladder_c02019 n (by omega) (by omega)
      · -- n <= 1313069310923
        rcases Nat.lt_or_ge 1303114069391 n with h8 | h8
        · -- n > 1303114069391
          rcases Nat.lt_or_ge 1306424114399 n with h10 | h10
          · -- n > 1306424114399
            rcases Nat.lt_or_ge 1309742521211 n with h12 | h12
            · -- n > 1309742521211
              exact RamareSaouter2003.prime_interval_nat_ladder_c02018 n (by omega) (by omega)
            · -- n <= 1309742521211
              exact RamareSaouter2003.prime_interval_nat_ladder_c02017 n (by omega) (by omega)
          · -- n <= 1306424114399
            exact RamareSaouter2003.prime_interval_nat_ladder_c02016 n (by omega) (by omega)
        · -- n <= 1303114069391
          rcases Nat.lt_or_ge 1296518981227 n with h10 | h10
          · -- n > 1296518981227
            rcases Nat.lt_or_ge 1299812365331 n with h12 | h12
            · -- n > 1299812365331
              exact RamareSaouter2003.prime_interval_nat_ladder_c02015 n (by omega) (by omega)
            · -- n <= 1299812365331
              exact RamareSaouter2003.prime_interval_nat_ladder_c02014 n (by omega) (by omega)
          · -- n <= 1296518981227
            exact RamareSaouter2003.prime_interval_nat_ladder_c02013 n (by omega) (by omega)
    · -- n <= 1293233896243
      rcases Nat.lt_or_ge 1273696507283 n with h6 | h6
      · -- n > 1273696507283
        rcases Nat.lt_or_ge 1283428228441 n with h8 | h8
        · -- n > 1283428228441
          rcases Nat.lt_or_ge 1286688540551 n with h10 | h10
          · -- n > 1286688540551
            rcases Nat.lt_or_ge 1289957089601 n with h12 | h12
            · -- n > 1289957089601
              exact RamareSaouter2003.prime_interval_nat_ladder_c02012 n (by omega) (by omega)
            · -- n <= 1289957089601
              exact RamareSaouter2003.prime_interval_nat_ladder_c02011 n (by omega) (by omega)
          · -- n <= 1286688540551
            exact RamareSaouter2003.prime_interval_nat_ladder_c02010 n (by omega) (by omega)
        · -- n <= 1283428228441
          rcases Nat.lt_or_ge 1276932232391 n with h10 | h10
          · -- n > 1276932232391
            rcases Nat.lt_or_ge 1280176132607 n with h12 | h12
            · -- n > 1280176132607
              exact RamareSaouter2003.prime_interval_nat_ladder_c02009 n (by omega) (by omega)
            · -- n <= 1280176132607
              exact RamareSaouter2003.prime_interval_nat_ladder_c02008 n (by omega) (by omega)
          · -- n <= 1276932232391
            exact RamareSaouter2003.prime_interval_nat_ladder_c02007 n (by omega) (by omega)
      · -- n <= 1273696507283
        rcases Nat.lt_or_ge 1264038178217 n with h8 | h8
        · -- n > 1264038178217
          rcases Nat.lt_or_ge 1267249500551 n with h10 | h10
          · -- n > 1267249500551
            rcases Nat.lt_or_ge 1270468936819 n with h12 | h12
            · -- n > 1270468936819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02006 n (by omega) (by omega)
            · -- n <= 1270468936819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02005 n (by omega) (by omega)
          · -- n <= 1267249500551
            exact RamareSaouter2003.prime_interval_nat_ladder_c02004 n (by omega) (by omega)
        · -- n <= 1264038178217
          rcases Nat.lt_or_ge 1257639793489 n with h10 | h10
          · -- n > 1257639793489
            rcases Nat.lt_or_ge 1260834949267 n with h12 | h12
            · -- n > 1260834949267
              exact RamareSaouter2003.prime_interval_nat_ladder_c02003 n (by omega) (by omega)
            · -- n <= 1260834949267
              exact RamareSaouter2003.prime_interval_nat_ladder_c02002 n (by omega) (by omega)
          · -- n <= 1257639793489
            exact RamareSaouter2003.prime_interval_nat_ladder_c02001 n (by omega) (by omega)
