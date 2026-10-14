-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T13:14:23.896837+00:00
-- url     : https://prove2.me/submissions/8c0cab2e-856d-44d3-9540-d18bae2ce924

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08200
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08227

theorem solution (n : Nat)
    (hn : 23850902211042336817 < n) (hupper : n <= 26882311053914850133) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 25290386988685136243 n with h2 | h2
  · -- n > 25290386988685136243
    rcases Nat.lt_or_ge 26042388632405942899 n with h4 | h4
    · -- n > 26042388632405942899
      rcases Nat.lt_or_ge 26426733418829301167 n with h6 | h6
      · -- n > 26426733418829301167
        rcases Nat.lt_or_ge 26621027788041003181 n with h8 | h8
        · -- n > 26621027788041003181
          rcases Nat.lt_or_ge 26751350449365758201 n with h10 | h10
          · -- n > 26751350449365758201
            rcases Nat.lt_or_ge 26816750785894489361 n with h12 | h12
            · -- n > 26816750785894489361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08227 n (by omega) (by omega)
            · -- n <= 26816750785894489361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08226 n (by omega) (by omega)
          · -- n <= 26751350449365758201
            rcases Nat.lt_or_ge 26686109585076461269 n with h12 | h12
            · -- n > 26686109585076461269
              exact RamareSaouter2003.prime_interval_nat_ladder_c08225 n (by omega) (by omega)
            · -- n <= 26686109585076461269
              exact RamareSaouter2003.prime_interval_nat_ladder_c08224 n (by omega) (by omega)
        · -- n <= 26621027788041003181
          rcases Nat.lt_or_ge 26491340180596318507 n with h10 | h10
          · -- n > 26491340180596318507
            rcases Nat.lt_or_ge 26556104777273577271 n with h12 | h12
            · -- n > 26556104777273577271
              exact RamareSaouter2003.prime_interval_nat_ladder_c08223 n (by omega) (by omega)
            · -- n <= 26556104777273577271
              exact RamareSaouter2003.prime_interval_nat_ladder_c08222 n (by omega) (by omega)
          · -- n <= 26491340180596318507
            exact RamareSaouter2003.prime_interval_nat_ladder_c08221 n (by omega) (by omega)
      · -- n <= 26426733418829301167
        rcases Nat.lt_or_ge 26233857180479387597 n with h8 | h8
        · -- n > 26233857180479387597
          rcases Nat.lt_or_ge 26297992186762941037 n with h10 | h10
          · -- n > 26297992186762941037
            rcases Nat.lt_or_ge 26362284162868341283 n with h12 | h12
            · -- n > 26362284162868341283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08220 n (by omega) (by omega)
            · -- n <= 26362284162868341283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08219 n (by omega) (by omega)
          · -- n <= 26297992186762941037
            exact RamareSaouter2003.prime_interval_nat_ladder_c08218 n (by omega) (by omega)
        · -- n <= 26233857180479387597
          rcases Nat.lt_or_ge 26106055786517971393 n with h10 | h10
          · -- n > 26106055786517971393
            rcases Nat.lt_or_ge 26169878428228872037 n with h12 | h12
            · -- n > 26169878428228872037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08217 n (by omega) (by omega)
            · -- n <= 26169878428228872037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08216 n (by omega) (by omega)
          · -- n <= 26106055786517971393
            exact RamareSaouter2003.prime_interval_nat_ladder_c08215 n (by omega) (by omega)
    · -- n <= 26042388632405942899
      rcases Nat.lt_or_ge 25663633561915073489 n with h6 | h6
      · -- n > 25663633561915073489
        rcases Nat.lt_or_ge 25852317623512062937 n with h8 | h8
        · -- n > 25852317623512062937
          rcases Nat.lt_or_ge 25915520028114836803 n with h10 | h10
          · -- n > 25915520028114836803
            rcases Nat.lt_or_ge 25978877028859933261 n with h12 | h12
            · -- n > 25978877028859933261
              exact RamareSaouter2003.prime_interval_nat_ladder_c08214 n (by omega) (by omega)
            · -- n <= 25978877028859933261
              exact RamareSaouter2003.prime_interval_nat_ladder_c08213 n (by omega) (by omega)
          · -- n <= 25915520028114836803
            exact RamareSaouter2003.prime_interval_nat_ladder_c08212 n (by omega) (by omega)
        · -- n <= 25852317623512062937
          rcases Nat.lt_or_ge 25726374797853309353 n with h10 | h10
          · -- n > 25726374797853309353
            rcases Nat.lt_or_ge 25789269216225267007 n with h12 | h12
            · -- n > 25789269216225267007
              exact RamareSaouter2003.prime_interval_nat_ladder_c08211 n (by omega) (by omega)
            · -- n <= 25789269216225267007
              exact RamareSaouter2003.prime_interval_nat_ladder_c08210 n (by omega) (by omega)
          · -- n <= 25726374797853309353
            exact RamareSaouter2003.prime_interval_nat_ladder_c08209 n (by omega) (by omega)
      · -- n <= 25663633561915073489
        rcases Nat.lt_or_ge 25476326934818435017 n with h8 | h8
        · -- n > 25476326934818435017
          rcases Nat.lt_or_ge 25538609772090245293 n with h10 | h10
          · -- n > 25538609772090245293
            rcases Nat.lt_or_ge 25601045326608603437 n with h12 | h12
            · -- n > 25601045326608603437
              exact RamareSaouter2003.prime_interval_nat_ladder_c08208 n (by omega) (by omega)
            · -- n <= 25601045326608603437
              exact RamareSaouter2003.prime_interval_nat_ladder_c08207 n (by omega) (by omega)
          · -- n <= 25538609772090245293
            exact RamareSaouter2003.prime_interval_nat_ladder_c08206 n (by omega) (by omega)
        · -- n <= 25476326934818435017
          rcases Nat.lt_or_ge 25352215722294968077 n with h10 | h10
          · -- n > 25352215722294968077
            rcases Nat.lt_or_ge 25414195623472449839 n with h12 | h12
            · -- n > 25414195623472449839
              exact RamareSaouter2003.prime_interval_nat_ladder_c08205 n (by omega) (by omega)
            · -- n <= 25414195623472449839
              exact RamareSaouter2003.prime_interval_nat_ladder_c08204 n (by omega) (by omega)
          · -- n <= 25352215722294968077
            exact RamareSaouter2003.prime_interval_nat_ladder_c08203 n (by omega) (by omega)
  · -- n <= 25290386988685136243
    rcases Nat.lt_or_ge 24560100565927501177 n with h4 | h4
    · -- n > 24560100565927501177
      rcases Nat.lt_or_ge 24922569079283136461 n with h6 | h6
      · -- n > 24922569079283136461
        rcases Nat.lt_or_ge 25105804607889843419 n with h8 | h8
        · -- n > 25105804607889843419
          rcases Nat.lt_or_ge 25167181807085135269 n with h10 | h10
          · -- n > 25167181807085135269
            rcases Nat.lt_or_ge 25228709353282018487 n with h12 | h12
            · -- n > 25228709353282018487
              exact RamareSaouter2003.prime_interval_nat_ladder_c08202 n (by omega) (by omega)
            · -- n <= 25228709353282018487
              exact RamareSaouter2003.prime_interval_nat_ladder_c08201 n (by omega) (by omega)
          · -- n <= 25167181807085135269
            exact RamareSaouter2003.prime_interval_nat_ladder_c08200 n (by omega) (by omega)
        · -- n <= 25105804607889843419
          rcases Nat.lt_or_ge 24983498447044929053 n with h10 | h10
          · -- n > 24983498447044929053
            rcases Nat.lt_or_ge 25044576848754520091 n with h12 | h12
            · -- n > 25044576848754520091
              exact RamareSaouter2003.prime_interval_nat_ladder_c08199 n (by omega) (by omega)
            · -- n <= 25044576848754520091
              exact RamareSaouter2003.prime_interval_nat_ladder_c08198 n (by omega) (by omega)
          · -- n <= 24983498447044929053
            exact RamareSaouter2003.prime_interval_nat_ladder_c08197 n (by omega) (by omega)
      · -- n <= 24922569079283136461
        rcases Nat.lt_or_ge 24740670930072460423 n with h8 | h8
        · -- n > 24740670930072460423
          rcases Nat.lt_or_ge 24801155716754278007 n with h10 | h10
          · -- n > 24801155716754278007
            rcases Nat.lt_or_ge 24861788312809377547 n with h12 | h12
            · -- n > 24861788312809377547
              exact RamareSaouter2003.prime_interval_nat_ladder_c08196 n (by omega) (by omega)
            · -- n <= 24861788312809377547
              exact RamareSaouter2003.prime_interval_nat_ladder_c08195 n (by omega) (by omega)
          · -- n <= 24801155716754278007
            exact RamareSaouter2003.prime_interval_nat_ladder_c08194 n (by omega) (by omega)
        · -- n <= 24740670930072460423
          rcases Nat.lt_or_ge 24620143674096910651 n with h10 | h10
          · -- n > 24620143674096910651
            rcases Nat.lt_or_ge 24680333682432689603 n with h12 | h12
            · -- n > 24680333682432689603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08193 n (by omega) (by omega)
            · -- n <= 24680333682432689603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08192 n (by omega) (by omega)
          · -- n <= 24620143674096910651
            exact RamareSaouter2003.prime_interval_nat_ladder_c08191 n (by omega) (by omega)
    · -- n <= 24560100565927501177
      rcases Nat.lt_or_ge 24202903926318152339 n with h6 | h6
      · -- n > 24202903926318152339
        rcases Nat.lt_or_ge 24380848482142410149 n with h8 | h8
        · -- n > 24380848482142410149
          rcases Nat.lt_or_ge 24440453449946679953 n with h10 | h10
          · -- n > 24440453449946679953
            rcases Nat.lt_or_ge 24500203909754428841 n with h12 | h12
            · -- n > 24500203909754428841
              exact RamareSaouter2003.prime_interval_nat_ladder_c08190 n (by omega) (by omega)
            · -- n <= 24500203909754428841
              exact RamareSaouter2003.prime_interval_nat_ladder_c08189 n (by omega) (by omega)
          · -- n <= 24440453449946679953
            exact RamareSaouter2003.prime_interval_nat_ladder_c08188 n (by omega) (by omega)
        · -- n <= 24380848482142410149
          rcases Nat.lt_or_ge 24262074009888404087 n with h10 | h10
          · -- n > 24262074009888404087
            rcases Nat.lt_or_ge 24321388741491548983 n with h12 | h12
            · -- n > 24321388741491548983
              exact RamareSaouter2003.prime_interval_nat_ladder_c08187 n (by omega) (by omega)
            · -- n <= 24321388741491548983
              exact RamareSaouter2003.prime_interval_nat_ladder_c08186 n (by omega) (by omega)
          · -- n <= 24262074009888404087
            exact RamareSaouter2003.prime_interval_nat_ladder_c08185 n (by omega) (by omega)
      · -- n <= 24202903926318152339
        rcases Nat.lt_or_ge 24026258436460418779 n with h8 | h8
        · -- n > 24026258436460418779
          rcases Nat.lt_or_ge 24084996462153258257 n with h10 | h10
          · -- n > 24084996462153258257
            rcases Nat.lt_or_ge 24143878281958614037 n with h12 | h12
            · -- n > 24143878281958614037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08184 n (by omega) (by omega)
            · -- n <= 24143878281958614037
              exact RamareSaouter2003.prime_interval_nat_ladder_c08183 n (by omega) (by omega)
          · -- n <= 24084996462153258257
            exact RamareSaouter2003.prime_interval_nat_ladder_c08182 n (by omega) (by omega)
        · -- n <= 24026258436460418779
          rcases Nat.lt_or_ge 23909211788113809413 n with h10 | h10
          · -- n > 23909211788113809413
            rcases Nat.lt_or_ge 23967663883808011387 n with h12 | h12
            · -- n > 23967663883808011387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08181 n (by omega) (by omega)
            · -- n <= 23967663883808011387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08180 n (by omega) (by omega)
          · -- n <= 23909211788113809413
            exact RamareSaouter2003.prime_interval_nat_ladder_c08179 n (by omega) (by omega)
