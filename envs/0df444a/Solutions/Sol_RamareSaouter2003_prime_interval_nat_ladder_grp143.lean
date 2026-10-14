-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T04:51:05.842309+00:00
-- url     : https://prove2.me/submissions/5d264ac2-c126-4cc4-b2ae-a7ea176eff2c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07149

theorem solution (n : Nat)
    (hn : 1178786480577465181 < n) (hupper : n <= 1353944432269289611) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1261548803847268483 n with h2 | h2
  · -- n > 1261548803847268483
    rcases Nat.lt_or_ge 1305084074806593203 n with h4 | h4
    · -- n > 1305084074806593203
      rcases Nat.lt_or_ge 1327412022538699333 n with h6 | h6
      · -- n > 1327412022538699333
        rcases Nat.lt_or_ge 1338718666082791901 n with h8 | h8
        · -- n > 1338718666082791901
          rcases Nat.lt_or_ge 1346310033571174643 n with h10 | h10
          · -- n > 1346310033571174643
            rcases Nat.lt_or_ge 1350121847271491977 n with h12 | h12
            · -- n > 1350121847271491977
              exact RamareSaouter2003.prime_interval_nat_ladder_c07149 n (by omega) (by omega)
            · -- n <= 1350121847271491977
              exact RamareSaouter2003.prime_interval_nat_ladder_c07148 n (by omega) (by omega)
          · -- n <= 1346310033571174643
            rcases Nat.lt_or_ge 1342508982383126353 n with h12 | h12
            · -- n > 1342508982383126353
              exact RamareSaouter2003.prime_interval_nat_ladder_c07147 n (by omega) (by omega)
            · -- n <= 1342508982383126353
              exact RamareSaouter2003.prime_interval_nat_ladder_c07146 n (by omega) (by omega)
        · -- n <= 1338718666082791901
          rcases Nat.lt_or_ge 1331170314057418717 n with h10 | h10
          · -- n > 1331170314057418717
            rcases Nat.lt_or_ge 1334939152306073023 n with h12 | h12
            · -- n > 1334939152306073023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07145 n (by omega) (by omega)
            · -- n <= 1334939152306073023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07144 n (by omega) (by omega)
          · -- n <= 1331170314057418717
            exact RamareSaouter2003.prime_interval_nat_ladder_c07143 n (by omega) (by omega)
      · -- n <= 1327412022538699333
        rcases Nat.lt_or_ge 1316200698828449887 n with h8 | h8
        · -- n > 1316200698828449887
          rcases Nat.lt_or_ge 1319927248912351721 n with h10 | h10
          · -- n > 1319927248912351721
            rcases Nat.lt_or_ge 1323664352420169047 n with h12 | h12
            · -- n > 1323664352420169047
              exact RamareSaouter2003.prime_interval_nat_ladder_c07142 n (by omega) (by omega)
            · -- n <= 1323664352420169047
              exact RamareSaouter2003.prime_interval_nat_ladder_c07141 n (by omega) (by omega)
          · -- n <= 1319927248912351721
            exact RamareSaouter2003.prime_interval_nat_ladder_c07140 n (by omega) (by omega)
        · -- n <= 1316200698828449887
          rcases Nat.lt_or_ge 1308779141993715697 n with h10 | h10
          · -- n > 1308779141993715697
            rcases Nat.lt_or_ge 1312484652280368871 n with h12 | h12
            · -- n > 1312484652280368871
              exact RamareSaouter2003.prime_interval_nat_ladder_c07139 n (by omega) (by omega)
            · -- n <= 1312484652280368871
              exact RamareSaouter2003.prime_interval_nat_ladder_c07138 n (by omega) (by omega)
          · -- n <= 1308779141993715697
            exact RamareSaouter2003.prime_interval_nat_ladder_c07137 n (by omega) (by omega)
    · -- n <= 1305084074806593203
      rcases Nat.lt_or_ge 1283131678982164261 n with h6 | h6
      · -- n > 1283131678982164261
        rcases Nat.lt_or_ge 1294061324160156241 n with h8 | h8
        · -- n > 1294061324160156241
          rcases Nat.lt_or_ge 1297725206181910267 n with h10 | h10
          · -- n > 1297725206181910267
            rcases Nat.lt_or_ge 1301399423913979469 n with h12 | h12
            · -- n > 1301399423913979469
              exact RamareSaouter2003.prime_interval_nat_ladder_c07136 n (by omega) (by omega)
            · -- n <= 1301399423913979469
              exact RamareSaouter2003.prime_interval_nat_ladder_c07135 n (by omega) (by omega)
          · -- n <= 1297725206181910267
            exact RamareSaouter2003.prime_interval_nat_ladder_c07134 n (by omega) (by omega)
        · -- n <= 1294061324160156241
          rcases Nat.lt_or_ge 1286764584699078239 n with h10 | h10
          · -- n > 1286764584699078239
            rcases Nat.lt_or_ge 1290407810730828011 n with h12 | h12
            · -- n > 1290407810730828011
              exact RamareSaouter2003.prime_interval_nat_ladder_c07133 n (by omega) (by omega)
            · -- n <= 1290407810730828011
              exact RamareSaouter2003.prime_interval_nat_ladder_c07132 n (by omega) (by omega)
          · -- n <= 1286764584699078239
            exact RamareSaouter2003.prime_interval_nat_ladder_c07131 n (by omega) (by omega)
      · -- n <= 1283131678982164261
        rcases Nat.lt_or_ge 1272294446521715989 n with h8 | h8
        · -- n > 1272294446521715989
          rcases Nat.lt_or_ge 1275896658710389357 n with h10 | h10
          · -- n > 1275896658710389357
            rcases Nat.lt_or_ge 1279509003457452011 n with h12 | h12
            · -- n > 1279509003457452011
              exact RamareSaouter2003.prime_interval_nat_ladder_c07130 n (by omega) (by omega)
            · -- n <= 1279509003457452011
              exact RamareSaouter2003.prime_interval_nat_ladder_c07129 n (by omega) (by omega)
          · -- n <= 1275896658710389357
            exact RamareSaouter2003.prime_interval_nat_ladder_c07128 n (by omega) (by omega)
        · -- n <= 1272294446521715989
          rcases Nat.lt_or_ge 1265120480796966967 n with h10 | h10
          · -- n > 1265120480796966967
            rcases Nat.lt_or_ge 1268702372760500023 n with h12 | h12
            · -- n > 1268702372760500023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07127 n (by omega) (by omega)
            · -- n <= 1268702372760500023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07126 n (by omega) (by omega)
          · -- n <= 1265120480796966967
            exact RamareSaouter2003.prime_interval_nat_ladder_c07125 n (by omega) (by omega)
  · -- n <= 1261548803847268483
    rcases Nat.lt_or_ge 1219465769770462943 n with h4 | h4
    · -- n > 1219465769770462943
      rcases Nat.lt_or_ge 1240328875918811093 n with h6 | h6
      · -- n > 1240328875918811093
        rcases Nat.lt_or_ge 1250893876034945189 n with h8 | h8
        · -- n > 1250893876034945189
          rcases Nat.lt_or_ge 1254435449603895371 n with h10 | h10
          · -- n > 1254435449603895371
            rcases Nat.lt_or_ge 1257987130739145649 n with h12 | h12
            · -- n > 1257987130739145649
              exact RamareSaouter2003.prime_interval_nat_ladder_c07124 n (by omega) (by omega)
            · -- n <= 1257987130739145649
              exact RamareSaouter2003.prime_interval_nat_ladder_c07123 n (by omega) (by omega)
          · -- n <= 1254435449603895371
            exact RamareSaouter2003.prime_interval_nat_ladder_c07122 n (by omega) (by omega)
        · -- n <= 1250893876034945189
          rcases Nat.lt_or_ge 1243840567744184519 n with h10 | h10
          · -- n > 1243840567744184519
            rcases Nat.lt_or_ge 1247362240854987833 n with h12 | h12
            · -- n > 1247362240854987833
              exact RamareSaouter2003.prime_interval_nat_ladder_c07121 n (by omega) (by omega)
            · -- n <= 1247362240854987833
              exact RamareSaouter2003.prime_interval_nat_ladder_c07120 n (by omega) (by omega)
          · -- n <= 1243840567744184519
            exact RamareSaouter2003.prime_interval_nat_ladder_c07119 n (by omega) (by omega)
      · -- n <= 1240328875918811093
        rcases Nat.lt_or_ge 1229853022283068009 n with h8 | h8
        · -- n > 1229853022283068009
          rcases Nat.lt_or_ge 1233335104041449147 n with h10 | h10
          · -- n > 1233335104041449147
            rcases Nat.lt_or_ge 1236827041566842647 n with h12 | h12
            · -- n > 1236827041566842647
              exact RamareSaouter2003.prime_interval_nat_ladder_c07118 n (by omega) (by omega)
            · -- n <= 1236827041566842647
              exact RamareSaouter2003.prime_interval_nat_ladder_c07117 n (by omega) (by omega)
          · -- n <= 1233335104041449147
            exact RamareSaouter2003.prime_interval_nat_ladder_c07116 n (by omega) (by omega)
        · -- n <= 1229853022283068009
          rcases Nat.lt_or_ge 1222918435783164629 n with h10 | h10
          · -- n > 1222918435783164629
            rcases Nat.lt_or_ge 1226380808752873129 n with h12 | h12
            · -- n > 1226380808752873129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07115 n (by omega) (by omega)
            · -- n <= 1226380808752873129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07114 n (by omega) (by omega)
          · -- n <= 1222918435783164629
            exact RamareSaouter2003.prime_interval_nat_ladder_c07113 n (by omega) (by omega)
    · -- n <= 1219465769770462943
      rcases Nat.lt_or_ge 1198953639349322873 n with h6 | h6
      · -- n > 1198953639349322873
        rcases Nat.lt_or_ge 1209166275810566653 n with h8 | h8
        · -- n > 1209166275810566653
          rcases Nat.lt_or_ge 1212589703838662491 n with h10 | h10
          · -- n > 1212589703838662491
            rcases Nat.lt_or_ge 1216022898437096479 n with h12 | h12
            · -- n > 1216022898437096479
              exact RamareSaouter2003.prime_interval_nat_ladder_c07112 n (by omega) (by omega)
            · -- n <= 1216022898437096479
              exact RamareSaouter2003.prime_interval_nat_ladder_c07111 n (by omega) (by omega)
          · -- n <= 1212589703838662491
            exact RamareSaouter2003.prime_interval_nat_ladder_c07110 n (by omega) (by omega)
        · -- n <= 1209166275810566653
          rcases Nat.lt_or_ge 1202348231996293289 n with h10 | h10
          · -- n > 1202348231996293289
            rcases Nat.lt_or_ge 1205752435164817913 n with h12 | h12
            · -- n > 1205752435164817913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07109 n (by omega) (by omega)
            · -- n <= 1205752435164817913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07108 n (by omega) (by omega)
          · -- n <= 1202348231996293289
            exact RamareSaouter2003.prime_interval_nat_ladder_c07107 n (by omega) (by omega)
      · -- n <= 1198953639349322873
        rcases Nat.lt_or_ge 1188827320761865601 n with h8 | h8
        · -- n > 1188827320761865601
          rcases Nat.lt_or_ge 1192193217078027589 n with h10 | h10
          · -- n > 1192193217078027589
            rcases Nat.lt_or_ge 1195568660866762739 n with h12 | h12
            · -- n > 1195568660866762739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07106 n (by omega) (by omega)
            · -- n <= 1195568660866762739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07105 n (by omega) (by omega)
          · -- n <= 1192193217078027589
            exact RamareSaouter2003.prime_interval_nat_ladder_c07104 n (by omega) (by omega)
        · -- n <= 1188827320761865601
          rcases Nat.lt_or_ge 1182123964986060949 n with h10 | h10
          · -- n > 1182123964986060949
            rcases Nat.lt_or_ge 1185470905665116827 n with h12 | h12
            · -- n > 1185470905665116827
              exact RamareSaouter2003.prime_interval_nat_ladder_c07103 n (by omega) (by omega)
            · -- n <= 1185470905665116827
              exact RamareSaouter2003.prime_interval_nat_ladder_c07102 n (by omega) (by omega)
          · -- n <= 1182123964986060949
            exact RamareSaouter2003.prime_interval_nat_ladder_c07101 n (by omega) (by omega)
