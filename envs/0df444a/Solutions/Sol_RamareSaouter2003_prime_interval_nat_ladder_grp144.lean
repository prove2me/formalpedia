-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T05:01:29.748843+00:00
-- url     : https://prove2.me/submissions/f198694c-027e-44f8-ada4-5377fca95c65

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07150
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07198

theorem solution (n : Nat)
    (hn : 1353944432269289611 < n) (hupper : n <= 1555129419536567443) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1449004642313285557 n with h2 | h2
  · -- n > 1449004642313285557
    rcases Nat.lt_or_ge 1499008970861312311 n with h4 | h4
    · -- n > 1499008970861312311
      rcases Nat.lt_or_ge 1524654535970435491 n with h6 | h6
      · -- n > 1524654535970435491
        rcases Nat.lt_or_ge 1537641405401029399 n with h8 | h8
        · -- n > 1537641405401029399
          rcases Nat.lt_or_ge 1546360661110009807 n with h10 | h10
          · -- n > 1546360661110009807
            rcases Nat.lt_or_ge 1550738828156977009 n with h12 | h12
            · -- n > 1550738828156977009
              exact RamareSaouter2003.prime_interval_nat_ladder_c07198 n (by omega) (by omega)
            · -- n <= 1550738828156977009
              exact RamareSaouter2003.prime_interval_nat_ladder_c07197 n (by omega) (by omega)
          · -- n <= 1546360661110009807
            rcases Nat.lt_or_ge 1541994916968289919 n with h12 | h12
            · -- n > 1541994916968289919
              exact RamareSaouter2003.prime_interval_nat_ladder_c07196 n (by omega) (by omega)
            · -- n <= 1541994916968289919
              exact RamareSaouter2003.prime_interval_nat_ladder_c07195 n (by omega) (by omega)
        · -- n <= 1537641405401029399
          rcases Nat.lt_or_ge 1528971301522712419 n with h10 | h10
          · -- n > 1528971301522712419
            rcases Nat.lt_or_ge 1533300266797270987 n with h12 | h12
            · -- n > 1533300266797270987
              exact RamareSaouter2003.prime_interval_nat_ladder_c07194 n (by omega) (by omega)
            · -- n <= 1533300266797270987
              exact RamareSaouter2003.prime_interval_nat_ladder_c07193 n (by omega) (by omega)
          · -- n <= 1528971301522712419
            exact RamareSaouter2003.prime_interval_nat_ladder_c07192 n (by omega) (by omega)
      · -- n <= 1524654535970435491
        rcases Nat.lt_or_ge 1511777338672800347 n with h8 | h8
        · -- n > 1511777338672800347
          rcases Nat.lt_or_ge 1516057588957695617 n with h10 | h10
          · -- n > 1516057588957695617
            rcases Nat.lt_or_ge 1520349958918569643 n with h12 | h12
            · -- n > 1520349958918569643
              exact RamareSaouter2003.prime_interval_nat_ladder_c07191 n (by omega) (by omega)
            · -- n <= 1520349958918569643
              exact RamareSaouter2003.prime_interval_nat_ladder_c07190 n (by omega) (by omega)
          · -- n <= 1516057588957695617
            exact RamareSaouter2003.prime_interval_nat_ladder_c07189 n (by omega) (by omega)
        · -- n <= 1511777338672800347
          rcases Nat.lt_or_ge 1503253094411570849 n with h10 | h10
          · -- n > 1503253094411570849
            rcases Nat.lt_or_ge 1507509260955198329 n with h12 | h12
            · -- n > 1507509260955198329
              exact RamareSaouter2003.prime_interval_nat_ladder_c07188 n (by omega) (by omega)
            · -- n <= 1507509260955198329
              exact RamareSaouter2003.prime_interval_nat_ladder_c07187 n (by omega) (by omega)
          · -- n <= 1503253094411570849
            exact RamareSaouter2003.prime_interval_nat_ladder_c07186 n (by omega) (by omega)
    · -- n <= 1499008970861312311
      rcases Nat.lt_or_ge 1473794788143367267 n with h6 | h6
      · -- n > 1473794788143367267
        rcases Nat.lt_or_ge 1486348441039486859 n with h8 | h8
        · -- n > 1486348441039486859
          rcases Nat.lt_or_ge 1490556640220502923 n with h10 | h10
          · -- n > 1490556640220502923
            rcases Nat.lt_or_ge 1494776820583418429 n with h12 | h12
            · -- n > 1494776820583418429
              exact RamareSaouter2003.prime_interval_nat_ladder_c07185 n (by omega) (by omega)
            · -- n <= 1494776820583418429
              exact RamareSaouter2003.prime_interval_nat_ladder_c07184 n (by omega) (by omega)
          · -- n <= 1490556640220502923
            exact RamareSaouter2003.prime_interval_nat_ladder_c07183 n (by omega) (by omega)
        · -- n <= 1486348441039486859
          rcases Nat.lt_or_ge 1477967533975984397 n with h10 | h10
          · -- n > 1477967533975984397
            rcases Nat.lt_or_ge 1482152095198643287 n with h12 | h12
            · -- n > 1482152095198643287
              exact RamareSaouter2003.prime_interval_nat_ladder_c07182 n (by omega) (by omega)
            · -- n <= 1482152095198643287
              exact RamareSaouter2003.prime_interval_nat_ladder_c07181 n (by omega) (by omega)
          · -- n <= 1477967533975984397
            exact RamareSaouter2003.prime_interval_nat_ladder_c07180 n (by omega) (by omega)
      · -- n <= 1473794788143367267
        rcases Nat.lt_or_ge 1461347188828453799 n with h8 | h8
        · -- n > 1461347188828453799
          rcases Nat.lt_or_ge 1465484710826191129 n with h10 | h10
          · -- n > 1465484710826191129
            rcases Nat.lt_or_ge 1469633878773602057 n with h12 | h12
            · -- n > 1469633878773602057
              exact RamareSaouter2003.prime_interval_nat_ladder_c07179 n (by omega) (by omega)
            · -- n <= 1469633878773602057
              exact RamareSaouter2003.prime_interval_nat_ladder_c07178 n (by omega) (by omega)
          · -- n <= 1465484710826191129
            exact RamareSaouter2003.prime_interval_nat_ladder_c07177 n (by omega) (by omega)
        · -- n <= 1461347188828453799
          rcases Nat.lt_or_ge 1453107216707317709 n with h10 | h10
          · -- n > 1453107216707317709
            rcases Nat.lt_or_ge 1457221368196407901 n with h12 | h12
            · -- n > 1457221368196407901
              exact RamareSaouter2003.prime_interval_nat_ladder_c07176 n (by omega) (by omega)
            · -- n <= 1457221368196407901
              exact RamareSaouter2003.prime_interval_nat_ladder_c07175 n (by omega) (by omega)
          · -- n <= 1453107216707317709
            exact RamareSaouter2003.prime_interval_nat_ladder_c07174 n (by omega) (by omega)
  · -- n <= 1449004642313285557
    rcases Nat.lt_or_ge 1400668478505338629 n with h4 | h4
    · -- n > 1400668478505338629
      rcases Nat.lt_or_ge 1424631601336671337 n with h6 | h6
      · -- n > 1424631601336671337
        rcases Nat.lt_or_ge 1436766460565445319 n with h8 | h8
        · -- n > 1436766460565445319
          rcases Nat.lt_or_ge 1440834362254599539 n with h10 | h10
          · -- n > 1440834362254599539
            rcases Nat.lt_or_ge 1444913769584167499 n with h12 | h12
            · -- n > 1444913769584167499
              exact RamareSaouter2003.prime_interval_nat_ladder_c07173 n (by omega) (by omega)
            · -- n <= 1444913769584167499
              exact RamareSaouter2003.prime_interval_nat_ladder_c07172 n (by omega) (by omega)
          · -- n <= 1440834362254599539
            exact RamareSaouter2003.prime_interval_nat_ladder_c07171 n (by omega) (by omega)
        · -- n <= 1436766460565445319
          rcases Nat.lt_or_ge 1428665071119214213 n with h10 | h10
          · -- n > 1428665071119214213
            rcases Nat.lt_or_ge 1432710057755333909 n with h12 | h12
            · -- n > 1432710057755333909
              exact RamareSaouter2003.prime_interval_nat_ladder_c07170 n (by omega) (by omega)
            · -- n <= 1432710057755333909
              exact RamareSaouter2003.prime_interval_nat_ladder_c07169 n (by omega) (by omega)
          · -- n <= 1428665071119214213
            exact RamareSaouter2003.prime_interval_nat_ladder_c07168 n (by omega) (by omega)
      · -- n <= 1424631601336671337
        rcases Nat.lt_or_ge 1412599244278243367 n with h8 | h8
        · -- n > 1412599244278243367
          rcases Nat.lt_or_ge 1416598677353845541 n with h10 | h10
          · -- n > 1416598677353845541
            rcases Nat.lt_or_ge 1420609444661188757 n with h12 | h12
            · -- n > 1420609444661188757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07167 n (by omega) (by omega)
            · -- n <= 1420609444661188757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07166 n (by omega) (by omega)
          · -- n <= 1416598677353845541
            exact RamareSaouter2003.prime_interval_nat_ladder_c07165 n (by omega) (by omega)
        · -- n <= 1412599244278243367
          rcases Nat.lt_or_ge 1404634173535217587 n with h10 | h10
          · -- n > 1404634173535217587
            rcases Nat.lt_or_ge 1408611043180340033 n with h12 | h12
            · -- n > 1408611043180340033
              exact RamareSaouter2003.prime_interval_nat_ladder_c07164 n (by omega) (by omega)
            · -- n <= 1408611043180340033
              exact RamareSaouter2003.prime_interval_nat_ladder_c07163 n (by omega) (by omega)
          · -- n <= 1404634173535217587
            exact RamareSaouter2003.prime_interval_nat_ladder_c07162 n (by omega) (by omega)
    · -- n <= 1400668478505338629
      rcases Nat.lt_or_ge 1377108267584432129 n with h6 | h6
      · -- n > 1377108267584432129
        rcases Nat.lt_or_ge 1388838376436122613 n with h8 | h8
        · -- n > 1388838376436122613
          rcases Nat.lt_or_ge 1392770596832849869 n with h10 | h10
          · -- n > 1392770596832849869
            rcases Nat.lt_or_ge 1396713953854734859 n with h12 | h12
            · -- n > 1396713953854734859
              exact RamareSaouter2003.prime_interval_nat_ladder_c07161 n (by omega) (by omega)
            · -- n <= 1396713953854734859
              exact RamareSaouter2003.prime_interval_nat_ladder_c07160 n (by omega) (by omega)
          · -- n <= 1392770596832849869
            exact RamareSaouter2003.prime_interval_nat_ladder_c07159 n (by omega) (by omega)
        · -- n <= 1388838376436122613
          rcases Nat.lt_or_ge 1381007281421113531 n with h10 | h10
          · -- n > 1381007281421113531
            rcases Nat.lt_or_ge 1384917333738562271 n with h12 | h12
            · -- n > 1384917333738562271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07158 n (by omega) (by omega)
            · -- n <= 1384917333738562271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07157 n (by omega) (by omega)
          · -- n <= 1381007281421113531
            exact RamareSaouter2003.prime_interval_nat_ladder_c07156 n (by omega) (by omega)
      · -- n <= 1377108267584432129
        rcases Nat.lt_or_ge 1365477268026947059 n with h8 | h8
        · -- n > 1365477268026947059
          rcases Nat.lt_or_ge 1369343288845170011 n with h10 | h10
          · -- n > 1369343288845170011
            rcases Nat.lt_or_ge 1373220317597059781 n with h12 | h12
            · -- n > 1373220317597059781
              exact RamareSaouter2003.prime_interval_nat_ladder_c07155 n (by omega) (by omega)
            · -- n <= 1373220317597059781
              exact RamareSaouter2003.prime_interval_nat_ladder_c07154 n (by omega) (by omega)
          · -- n <= 1369343288845170011
            exact RamareSaouter2003.prime_interval_nat_ladder_c07153 n (by omega) (by omega)
        · -- n <= 1365477268026947059
          rcases Nat.lt_or_ge 1357777839386171767 n with h10 | h10
          · -- n > 1357777839386171767
            rcases Nat.lt_or_ge 1361622105587387359 n with h12 | h12
            · -- n > 1361622105587387359
              exact RamareSaouter2003.prime_interval_nat_ladder_c07152 n (by omega) (by omega)
            · -- n <= 1361622105587387359
              exact RamareSaouter2003.prime_interval_nat_ladder_c07151 n (by omega) (by omega)
          · -- n <= 1357777839386171767
            exact RamareSaouter2003.prime_interval_nat_ladder_c07150 n (by omega) (by omega)
