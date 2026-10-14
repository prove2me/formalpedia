-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T22:00:55.956003+00:00
-- url     : https://prove2.me/submissions/974aef1c-41f6-43df-a4b3-e5cf97554b16

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06250

theorem solution (n : Nat)
    (hn : 92548121498906519 < n) (hupper : n <= 106600483443424039) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 99326074659000479 n with h2 | h2
  · -- n > 99326074659000479
    rcases Nat.lt_or_ge 102753686259879397 n with h4 | h4
    · -- n > 102753686259879397
      rcases Nat.lt_or_ge 104511563897117263 n with h6 | h6
      · -- n > 104511563897117263
        rcases Nat.lt_or_ge 105401744248515277 n with h8 | h8
        · -- n > 105401744248515277
          rcases Nat.lt_or_ge 105999423666849287 n with h10 | h10
          · -- n > 105999423666849287
            rcases Nat.lt_or_ge 106299519439723013 n with h12 | h12
            · -- n > 106299519439723013
              exact RamareSaouter2003.prime_interval_nat_ladder_c06250 n (by omega) (by omega)
            · -- n <= 106299519439723013
              exact RamareSaouter2003.prime_interval_nat_ladder_c06249 n (by omega) (by omega)
          · -- n <= 105999423666849287
            rcases Nat.lt_or_ge 105700164982474483 n with h12 | h12
            · -- n > 105700164982474483
              exact RamareSaouter2003.prime_interval_nat_ladder_c06248 n (by omega) (by omega)
            · -- n <= 105700164982474483
              exact RamareSaouter2003.prime_interval_nat_ladder_c06247 n (by omega) (by omega)
        · -- n <= 105401744248515277
          rcases Nat.lt_or_ge 104807465270811047 n with h10 | h10
          · -- n > 104807465270811047
            rcases Nat.lt_or_ge 105104194060312079 n with h12 | h12
            · -- n > 105104194060312079
              exact RamareSaouter2003.prime_interval_nat_ladder_c06246 n (by omega) (by omega)
            · -- n <= 105104194060312079
              exact RamareSaouter2003.prime_interval_nat_ladder_c06245 n (by omega) (by omega)
          · -- n <= 104807465270811047
            exact RamareSaouter2003.prime_interval_nat_ladder_c06244 n (by omega) (by omega)
      · -- n <= 104511563897117263
        rcases Nat.lt_or_ge 103628885578730387 n with h8 | h8
        · -- n > 103628885578730387
          rcases Nat.lt_or_ge 103922261649549529 n with h10 | h10
          · -- n > 103922261649549529
            rcases Nat.lt_or_ge 104216496611346079 n with h12 | h12
            · -- n > 104216496611346079
              exact RamareSaouter2003.prime_interval_nat_ladder_c06243 n (by omega) (by omega)
            · -- n <= 104216496611346079
              exact RamareSaouter2003.prime_interval_nat_ladder_c06242 n (by omega) (by omega)
          · -- n <= 103922261649549529
            exact RamareSaouter2003.prime_interval_nat_ladder_c06241 n (by omega) (by omega)
        · -- n <= 103628885578730387
          rcases Nat.lt_or_ge 103044605120867989 n with h10 | h10
          · -- n > 103044605120867989
            rcases Nat.lt_or_ge 103336313852568143 n with h12 | h12
            · -- n > 103336313852568143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06240 n (by omega) (by omega)
            · -- n <= 103336313852568143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06239 n (by omega) (by omega)
          · -- n <= 103044605120867989
            exact RamareSaouter2003.prime_interval_nat_ladder_c06238 n (by omega) (by omega)
    · -- n <= 102753686259879397
      rcases Nat.lt_or_ge 101025345345185939 n with h6 | h6
      · -- n > 101025345345185939
        rcases Nat.lt_or_ge 101885852526352033 n with h8 | h8
        · -- n > 101885852526352033
          rcases Nat.lt_or_ge 102174313654457719 n with h10 | h10
          · -- n > 102174313654457719
            rcases Nat.lt_or_ge 102463580747417069 n with h12 | h12
            · -- n > 102463580747417069
              exact RamareSaouter2003.prime_interval_nat_ladder_c06237 n (by omega) (by omega)
            · -- n <= 102463580747417069
              exact RamareSaouter2003.prime_interval_nat_ladder_c06236 n (by omega) (by omega)
          · -- n <= 102174313654457719
            exact RamareSaouter2003.prime_interval_nat_ladder_c06235 n (by omega) (by omega)
        · -- n <= 101885852526352033
          rcases Nat.lt_or_ge 101311373920999673 n with h10 | h10
          · -- n > 101311373920999673
            rcases Nat.lt_or_ge 101598213542369641 n with h12 | h12
            · -- n > 101598213542369641
              exact RamareSaouter2003.prime_interval_nat_ladder_c06234 n (by omega) (by omega)
            · -- n <= 101598213542369641
              exact RamareSaouter2003.prime_interval_nat_ladder_c06233 n (by omega) (by omega)
          · -- n <= 101311373920999673
            exact RamareSaouter2003.prime_interval_nat_ladder_c06232 n (by omega) (by omega)
      · -- n <= 101025345345185939
        rcases Nat.lt_or_ge 100172092318629979 n with h8 | h8
        · -- n > 100172092318629979
          rcases Nat.lt_or_ge 100455705014127721 n with h10 | h10
          · -- n > 100455705014127721
            rcases Nat.lt_or_ge 100740125501197759 n with h12 | h12
            · -- n > 100740125501197759
              exact RamareSaouter2003.prime_interval_nat_ladder_c06231 n (by omega) (by omega)
            · -- n <= 100740125501197759
              exact RamareSaouter2003.prime_interval_nat_ladder_c06230 n (by omega) (by omega)
          · -- n <= 100455705014127721
            exact RamareSaouter2003.prime_interval_nat_ladder_c06229 n (by omega) (by omega)
        · -- n <= 100172092318629979
          rcases Nat.lt_or_ge 99607270358058259 n with h10 | h10
          · -- n > 99607270358058259
            rcases Nat.lt_or_ge 99889281998867071 n with h12 | h12
            · -- n > 99889281998867071
              exact RamareSaouter2003.prime_interval_nat_ladder_c06228 n (by omega) (by omega)
            · -- n <= 99889281998867071
              exact RamareSaouter2003.prime_interval_nat_ladder_c06227 n (by omega) (by omega)
          · -- n <= 99607270358058259
            exact RamareSaouter2003.prime_interval_nat_ladder_c06226 n (by omega) (by omega)
  · -- n <= 99326074659000479
    rcases Nat.lt_or_ge 95741824235603173 n with h4 | h4
    · -- n > 95741824235603173
      rcases Nat.lt_or_ge 97379711356031173 n with h6 | h6
      · -- n > 97379711356031173
        rcases Nat.lt_or_ge 98209115496321769 n with h8 | h8
        · -- n > 98209115496321769
          rcases Nat.lt_or_ge 98766016466324021 n with h10 | h10
          · -- n > 98766016466324021
            rcases Nat.lt_or_ge 99045652185527023 n with h12 | h12
            · -- n > 99045652185527023
              exact RamareSaouter2003.prime_interval_nat_ladder_c06225 n (by omega) (by omega)
            · -- n <= 99045652185527023
              exact RamareSaouter2003.prime_interval_nat_ladder_c06224 n (by omega) (by omega)
          · -- n <= 98766016466324021
            rcases Nat.lt_or_ge 98487175216616803 n with h12 | h12
            · -- n > 98487175216616803
              exact RamareSaouter2003.prime_interval_nat_ladder_c06223 n (by omega) (by omega)
            · -- n <= 98487175216616803
              exact RamareSaouter2003.prime_interval_nat_ladder_c06222 n (by omega) (by omega)
        · -- n <= 98209115496321769
          rcases Nat.lt_or_ge 97655422164306691 n with h10 | h10
          · -- n > 97655422164306691
            rcases Nat.lt_or_ge 97931848767798277 n with h12 | h12
            · -- n > 97931848767798277
              exact RamareSaouter2003.prime_interval_nat_ladder_c06221 n (by omega) (by omega)
            · -- n <= 97931848767798277
              exact RamareSaouter2003.prime_interval_nat_ladder_c06220 n (by omega) (by omega)
          · -- n <= 97655422164306691
            exact RamareSaouter2003.prime_interval_nat_ladder_c06219 n (by omega) (by omega)
      · -- n <= 97379711356031173
        rcases Nat.lt_or_ge 96557285318401319 n with h8 | h8
        · -- n > 96557285318401319
          rcases Nat.lt_or_ge 96830665171755661 n with h10 | h10
          · -- n > 96830665171755661
            rcases Nat.lt_or_ge 97104792926807423 n with h12 | h12
            · -- n > 97104792926807423
              exact RamareSaouter2003.prime_interval_nat_ladder_c06218 n (by omega) (by omega)
            · -- n <= 97104792926807423
              exact RamareSaouter2003.prime_interval_nat_ladder_c06217 n (by omega) (by omega)
          · -- n <= 96830665171755661
            exact RamareSaouter2003.prime_interval_nat_ladder_c06216 n (by omega) (by omega)
        · -- n <= 96557285318401319
          rcases Nat.lt_or_ge 96012866832572771 n with h10 | h10
          · -- n > 96012866832572771
            rcases Nat.lt_or_ge 96284693478795427 n with h12 | h12
            · -- n > 96284693478795427
              exact RamareSaouter2003.prime_interval_nat_ladder_c06215 n (by omega) (by omega)
            · -- n <= 96284693478795427
              exact RamareSaouter2003.prime_interval_nat_ladder_c06214 n (by omega) (by omega)
          · -- n <= 96012866832572771
            exact RamareSaouter2003.prime_interval_nat_ladder_c06213 n (by omega) (by omega)
    · -- n <= 95741824235603173
      rcases Nat.lt_or_ge 94131432457775179 n with h6 | h6
      · -- n > 94131432457775179
        rcases Nat.lt_or_ge 94933217121244331 n with h8 | h8
        · -- n > 94933217121244331
          rcases Nat.lt_or_ge 95201993543535917 n with h10 | h10
          · -- n > 95201993543535917
            rcases Nat.lt_or_ge 95471517553728499 n with h12 | h12
            · -- n > 95471517553728499
              exact RamareSaouter2003.prime_interval_nat_ladder_c06212 n (by omega) (by omega)
            · -- n <= 95471517553728499
              exact RamareSaouter2003.prime_interval_nat_ladder_c06211 n (by omega) (by omega)
          · -- n <= 95201993543535917
            exact RamareSaouter2003.prime_interval_nat_ladder_c06210 n (by omega) (by omega)
        · -- n <= 94933217121244331
          rcases Nat.lt_or_ge 94397939726900881 n with h10 | h10
          · -- n > 94397939726900881
            rcases Nat.lt_or_ge 94665208974255583 n with h12 | h12
            · -- n > 94665208974255583
              exact RamareSaouter2003.prime_interval_nat_ladder_c06209 n (by omega) (by omega)
            · -- n <= 94665208974255583
              exact RamareSaouter2003.prime_interval_nat_ladder_c06208 n (by omega) (by omega)
          · -- n <= 94397939726900881
            exact RamareSaouter2003.prime_interval_nat_ladder_c06207 n (by omega) (by omega)
      · -- n <= 94131432457775179
        rcases Nat.lt_or_ge 93336430575677843 n with h8 | h8
        · -- n > 93336430575677843
          rcases Nat.lt_or_ge 93600686201586449 n with h10 | h10
          · -- n > 93600686201586449
            rcases Nat.lt_or_ge 93865675687252169 n with h12 | h12
            · -- n > 93865675687252169
              exact RamareSaouter2003.prime_interval_nat_ladder_c06206 n (by omega) (by omega)
            · -- n <= 93865675687252169
              exact RamareSaouter2003.prime_interval_nat_ladder_c06205 n (by omega) (by omega)
          · -- n <= 93600686201586449
            exact RamareSaouter2003.prime_interval_nat_ladder_c06204 n (by omega) (by omega)
        · -- n <= 93336430575677843
          rcases Nat.lt_or_ge 92810149488179569 n with h10 | h10
          · -- n > 92810149488179569
            rcases Nat.lt_or_ge 93072921883394863 n with h12 | h12
            · -- n > 93072921883394863
              exact RamareSaouter2003.prime_interval_nat_ladder_c06203 n (by omega) (by omega)
            · -- n <= 93072921883394863
              exact RamareSaouter2003.prime_interval_nat_ladder_c06202 n (by omega) (by omega)
          · -- n <= 92810149488179569
            exact RamareSaouter2003.prime_interval_nat_ladder_c06201 n (by omega) (by omega)
