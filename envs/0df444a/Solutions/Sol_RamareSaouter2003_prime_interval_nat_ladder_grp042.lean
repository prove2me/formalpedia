-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T15:13:32.86132+00:00
-- url     : https://prove2.me/submissions/b9db1442-4e8d-436f-afac-43328a6f1391

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02100

theorem solution (n : Nat)
    (hn : 1424081223991 < n) (hupper : n <= 1616505218459) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1517262413551 n with h2 | h2
  · -- n > 1517262413551
    rcases Nat.lt_or_ge 1564118906827 n with h4 | h4
    · -- n > 1564118906827
      rcases Nat.lt_or_ge 1588084020587 n with h6 | h6
      · -- n > 1588084020587
        rcases Nat.lt_or_ge 1600203165469 n with h8 | h8
        · -- n > 1600203165469
          rcases Nat.lt_or_ge 1608333650239 n with h10 | h10
          · -- n > 1608333650239
            rcases Nat.lt_or_ge 1612414286047 n with h12 | h12
            · -- n > 1612414286047
              exact RamareSaouter2003.prime_interval_nat_ladder_c02100 n (by omega) (by omega)
            · -- n <= 1612414286047
              exact RamareSaouter2003.prime_interval_nat_ladder_c02099 n (by omega) (by omega)
          · -- n <= 1608333650239
            rcases Nat.lt_or_ge 1604263285277 n with h12 | h12
            · -- n > 1604263285277
              exact RamareSaouter2003.prime_interval_nat_ladder_c02098 n (by omega) (by omega)
            · -- n <= 1604263285277
              exact RamareSaouter2003.prime_interval_nat_ladder_c02097 n (by omega) (by omega)
        · -- n <= 1600203165469
          rcases Nat.lt_or_ge 1592113558703 n with h10 | h10
          · -- n > 1592113558703
            rcases Nat.lt_or_ge 1596153265171 n with h12 | h12
            · -- n > 1596153265171
              exact RamareSaouter2003.prime_interval_nat_ladder_c02096 n (by omega) (by omega)
            · -- n <= 1596153265171
              exact RamareSaouter2003.prime_interval_nat_ladder_c02095 n (by omega) (by omega)
          · -- n <= 1592113558703
            exact RamareSaouter2003.prime_interval_nat_ladder_c02094 n (by omega) (by omega)
      · -- n <= 1588084020587
        rcases Nat.lt_or_ge 1576056162259 n with h8 | h8
        · -- n > 1576056162259
          rcases Nat.lt_or_ge 1580055347753 n with h10 | h10
          · -- n > 1580055347753
            rcases Nat.lt_or_ge 1584064625399 n with h12 | h12
            · -- n > 1584064625399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02093 n (by omega) (by omega)
            · -- n <= 1584064625399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02092 n (by omega) (by omega)
          · -- n <= 1580055347753
            exact RamareSaouter2003.prime_interval_nat_ladder_c02091 n (by omega) (by omega)
        · -- n <= 1576056162259
          rcases Nat.lt_or_ge 1568087966987 n with h10 | h10
          · -- n > 1568087966987
            rcases Nat.lt_or_ge 1572067043747 n with h12 | h12
            · -- n > 1572067043747
              exact RamareSaouter2003.prime_interval_nat_ladder_c02090 n (by omega) (by omega)
            · -- n <= 1572067043747
              exact RamareSaouter2003.prime_interval_nat_ladder_c02089 n (by omega) (by omega)
          · -- n <= 1568087966987
            exact RamareSaouter2003.prime_interval_nat_ladder_c02088 n (by omega) (by omega)
    · -- n <= 1564118906827
      rcases Nat.lt_or_ge 1540513494407 n with h6 | h6
      · -- n > 1540513494407
        rcases Nat.lt_or_ge 1552271575447 n with h8 | h8
        · -- n > 1552271575447
          rcases Nat.lt_or_ge 1556210736011 n with h10 | h10
          · -- n > 1556210736011
            rcases Nat.lt_or_ge 1560159838177 n with h12 | h12
            · -- n > 1560159838177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02087 n (by omega) (by omega)
            · -- n <= 1560159838177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02086 n (by omega) (by omega)
          · -- n <= 1556210736011
            exact RamareSaouter2003.prime_interval_nat_ladder_c02085 n (by omega) (by omega)
        · -- n <= 1552271575447
          rcases Nat.lt_or_ge 1544422979329 n with h10 | h10
          · -- n > 1544422979329
            rcases Nat.lt_or_ge 1548342331463 n with h12 | h12
            · -- n > 1548342331463
              exact RamareSaouter2003.prime_interval_nat_ladder_c02084 n (by omega) (by omega)
            · -- n <= 1548342331463
              exact RamareSaouter2003.prime_interval_nat_ladder_c02083 n (by omega) (by omega)
          · -- n <= 1544422979329
            exact RamareSaouter2003.prime_interval_nat_ladder_c02082 n (by omega) (by omega)
      · -- n <= 1540513494407
        rcases Nat.lt_or_ge 1528843995017 n with h8 | h8
        · -- n > 1528843995017
          rcases Nat.lt_or_ge 1532724026839 n with h10 | h10
          · -- n > 1532724026839
            rcases Nat.lt_or_ge 1536613851779 n with h12 | h12
            · -- n > 1536613851779
              exact RamareSaouter2003.prime_interval_nat_ladder_c02081 n (by omega) (by omega)
            · -- n <= 1536613851779
              exact RamareSaouter2003.prime_interval_nat_ladder_c02080 n (by omega) (by omega)
          · -- n <= 1532724026839
            exact RamareSaouter2003.prime_interval_nat_ladder_c02079 n (by omega) (by omega)
        · -- n <= 1528843995017
          rcases Nat.lt_or_ge 1521113212813 n with h10 | h10
          · -- n > 1521113212813
            rcases Nat.lt_or_ge 1524973731847 n with h12 | h12
            · -- n > 1524973731847
              exact RamareSaouter2003.prime_interval_nat_ladder_c02078 n (by omega) (by omega)
            · -- n <= 1524973731847
              exact RamareSaouter2003.prime_interval_nat_ladder_c02077 n (by omega) (by omega)
          · -- n <= 1521113212813
            exact RamareSaouter2003.prime_interval_nat_ladder_c02076 n (by omega) (by omega)
  · -- n <= 1517262413551
    rcases Nat.lt_or_ge 1468075531513 n with h4 | h4
    · -- n > 1468075531513
      rcases Nat.lt_or_ge 1490576935781 n with h6 | h6
      · -- n > 1490576935781
        rcases Nat.lt_or_ge 1501955928511 n with h8 | h8
        · -- n > 1501955928511
          rcases Nat.lt_or_ge 1509589877137 n with h10 | h10
          · -- n > 1509589877137
            rcases Nat.lt_or_ge 1513421309801 n with h12 | h12
            · -- n > 1513421309801
              exact RamareSaouter2003.prime_interval_nat_ladder_c02075 n (by omega) (by omega)
            · -- n <= 1513421309801
              exact RamareSaouter2003.prime_interval_nat_ladder_c02074 n (by omega) (by omega)
          · -- n <= 1509589877137
            rcases Nat.lt_or_ge 1505768091463 n with h12 | h12
            · -- n > 1505768091463
              exact RamareSaouter2003.prime_interval_nat_ladder_c02073 n (by omega) (by omega)
            · -- n <= 1505768091463
              exact RamareSaouter2003.prime_interval_nat_ladder_c02072 n (by omega) (by omega)
        · -- n <= 1501955928511
          rcases Nat.lt_or_ge 1494360374713 n with h10 | h10
          · -- n > 1494360374713
            rcases Nat.lt_or_ge 1498153364263 n with h12 | h12
            · -- n > 1498153364263
              exact RamareSaouter2003.prime_interval_nat_ladder_c02071 n (by omega) (by omega)
            · -- n <= 1498153364263
              exact RamareSaouter2003.prime_interval_nat_ladder_c02070 n (by omega) (by omega)
          · -- n <= 1494360374713
            exact RamareSaouter2003.prime_interval_nat_ladder_c02069 n (by omega) (by omega)
      · -- n <= 1490576935781
        rcases Nat.lt_or_ge 1479283684289 n with h8 | h8
        · -- n > 1479283684289
          rcases Nat.lt_or_ge 1483038614419 n with h10 | h10
          · -- n > 1483038614419
            rcases Nat.lt_or_ge 1486803023633 n with h12 | h12
            · -- n > 1486803023633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02068 n (by omega) (by omega)
            · -- n <= 1486803023633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02067 n (by omega) (by omega)
          · -- n <= 1483038614419
            exact RamareSaouter2003.prime_interval_nat_ladder_c02066 n (by omega) (by omega)
        · -- n <= 1479283684289
          rcases Nat.lt_or_ge 1471802166491 n with h10 | h10
          · -- n > 1471802166491
            rcases Nat.lt_or_ge 1475538209507 n with h12 | h12
            · -- n > 1475538209507
              exact RamareSaouter2003.prime_interval_nat_ladder_c02065 n (by omega) (by omega)
            · -- n <= 1475538209507
              exact RamareSaouter2003.prime_interval_nat_ladder_c02064 n (by omega) (by omega)
          · -- n <= 1471802166491
            exact RamareSaouter2003.prime_interval_nat_ladder_c02063 n (by omega) (by omega)
    · -- n <= 1468075531513
      rcases Nat.lt_or_ge 1445911976063 n with h6 | h6
      · -- n > 1445911976063
        rcases Nat.lt_or_ge 1456951839901 n with h8 | h8
        · -- n > 1456951839901
          rcases Nat.lt_or_ge 1460650391803 n with h10 | h10
          · -- n > 1460650391803
            rcases Nat.lt_or_ge 1464358281019 n with h12 | h12
            · -- n > 1464358281019
              exact RamareSaouter2003.prime_interval_nat_ladder_c02062 n (by omega) (by omega)
            · -- n <= 1464358281019
              exact RamareSaouter2003.prime_interval_nat_ladder_c02061 n (by omega) (by omega)
          · -- n <= 1460650391803
            exact RamareSaouter2003.prime_interval_nat_ladder_c02060 n (by omega) (by omega)
        · -- n <= 1456951839901
          rcases Nat.lt_or_ge 1449582655357 n with h10 | h10
          · -- n > 1449582655357
            rcases Nat.lt_or_ge 1453262602219 n with h12 | h12
            · -- n > 1453262602219
              exact RamareSaouter2003.prime_interval_nat_ladder_c02059 n (by omega) (by omega)
            · -- n <= 1453262602219
              exact RamareSaouter2003.prime_interval_nat_ladder_c02058 n (by omega) (by omega)
          · -- n <= 1449582655357
            exact RamareSaouter2003.prime_interval_nat_ladder_c02057 n (by omega) (by omega)
      · -- n <= 1445911976063
        rcases Nat.lt_or_ge 1434955311929 n with h8 | h8
        · -- n > 1434955311929
          rcases Nat.lt_or_ge 1438598327489 n with h10 | h10
          · -- n > 1438598327489
            rcases Nat.lt_or_ge 1442250541157 n with h12 | h12
            · -- n > 1442250541157
              exact RamareSaouter2003.prime_interval_nat_ladder_c02056 n (by omega) (by omega)
            · -- n <= 1442250541157
              exact RamareSaouter2003.prime_interval_nat_ladder_c02055 n (by omega) (by omega)
          · -- n <= 1438598327489
            exact RamareSaouter2003.prime_interval_nat_ladder_c02054 n (by omega) (by omega)
        · -- n <= 1434955311929
          rcases Nat.lt_or_ge 1427696783197 n with h10 | h10
          · -- n > 1427696783197
            rcases Nat.lt_or_ge 1431321471467 n with h12 | h12
            · -- n > 1431321471467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02053 n (by omega) (by omega)
            · -- n <= 1431321471467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02052 n (by omega) (by omega)
          · -- n <= 1427696783197
            exact RamareSaouter2003.prime_interval_nat_ladder_c02051 n (by omega) (by omega)
