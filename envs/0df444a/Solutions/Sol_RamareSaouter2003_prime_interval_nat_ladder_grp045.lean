-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T17:10:23.737263+00:00
-- url     : https://prove2.me/submissions/c515c3de-7a03-4d52-b233-02137ca00d36

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02250

theorem solution (n : Nat)
    (hn : 2082320379773 < n) (hupper : n <= 2363065123879) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2218280052337 n with h2 | h2
  · -- n > 2218280052337
    rcases Nat.lt_or_ge 2286641242231 n with h4 | h4
    · -- n > 2286641242231
      rcases Nat.lt_or_ge 2321603447827 n with h6 | h6
      · -- n > 2321603447827
        rcases Nat.lt_or_ge 2339283398077 n with h8 | h8
        · -- n > 2339283398077
          rcases Nat.lt_or_ge 2351144356921 n with h10 | h10
          · -- n > 2351144356921
            rcases Nat.lt_or_ge 2357097245681 n with h12 | h12
            · -- n > 2357097245681
              exact RamareSaouter2003.prime_interval_nat_ladder_c02250 n (by omega) (by omega)
            · -- n <= 2357097245681
              exact RamareSaouter2003.prime_interval_nat_ladder_c02249 n (by omega) (by omega)
          · -- n <= 2351144356921
            rcases Nat.lt_or_ge 2345206420171 n with h12 | h12
            · -- n > 2345206420171
              exact RamareSaouter2003.prime_interval_nat_ladder_c02248 n (by omega) (by omega)
            · -- n <= 2345206420171
              exact RamareSaouter2003.prime_interval_nat_ladder_c02247 n (by omega) (by omega)
        · -- n <= 2339283398077
          rcases Nat.lt_or_ge 2327481949043 n with h10 | h10
          · -- n > 2327481949043
            rcases Nat.lt_or_ge 2333375253371 n with h12 | h12
            · -- n > 2333375253371
              exact RamareSaouter2003.prime_interval_nat_ladder_c02246 n (by omega) (by omega)
            · -- n <= 2333375253371
              exact RamareSaouter2003.prime_interval_nat_ladder_c02245 n (by omega) (by omega)
          · -- n <= 2327481949043
            exact RamareSaouter2003.prime_interval_nat_ladder_c02244 n (by omega) (by omega)
      · -- n <= 2321603447827
        rcases Nat.lt_or_ge 2304056393633 n with h8 | h8
        · -- n > 2304056393633
          rcases Nat.lt_or_ge 2309890706917 n with h10 | h10
          · -- n > 2309890706917
            rcases Nat.lt_or_ge 2315739712721 n with h12 | h12
            · -- n > 2315739712721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02243 n (by omega) (by omega)
            · -- n <= 2315739712721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02242 n (by omega) (by omega)
          · -- n <= 2309890706917
            exact RamareSaouter2003.prime_interval_nat_ladder_c02241 n (by omega) (by omega)
        · -- n <= 2304056393633
          rcases Nat.lt_or_ge 2292431697883 n with h10 | h10
          · -- n > 2292431697883
            rcases Nat.lt_or_ge 2298236736139 n with h12 | h12
            · -- n > 2298236736139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02240 n (by omega) (by omega)
            · -- n <= 2298236736139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02239 n (by omega) (by omega)
          · -- n <= 2292431697883
            exact RamareSaouter2003.prime_interval_nat_ladder_c02238 n (by omega) (by omega)
    · -- n <= 2286641242231
      rcases Nat.lt_or_ge 2252202710621 n with h6 | h6
      · -- n > 2252202710621
        rcases Nat.lt_or_ge 2269357007447 n with h8 | h8
        · -- n > 2269357007447
          rcases Nat.lt_or_ge 2275103933279 n with h10 | h10
          · -- n > 2275103933279
            rcases Nat.lt_or_ge 2280865332799 n with h12 | h12
            · -- n > 2280865332799
              exact RamareSaouter2003.prime_interval_nat_ladder_c02237 n (by omega) (by omega)
            · -- n <= 2280865332799
              exact RamareSaouter2003.prime_interval_nat_ladder_c02236 n (by omega) (by omega)
          · -- n <= 2275103933279
            exact RamareSaouter2003.prime_interval_nat_ladder_c02235 n (by omega) (by omega)
        · -- n <= 2269357007447
          rcases Nat.lt_or_ge 2257906432063 n with h10 | h10
          · -- n > 2257906432063
            rcases Nat.lt_or_ge 2263624519049 n with h12 | h12
            · -- n > 2263624519049
              exact RamareSaouter2003.prime_interval_nat_ladder_c02234 n (by omega) (by omega)
            · -- n <= 2263624519049
              exact RamareSaouter2003.prime_interval_nat_ladder_c02233 n (by omega) (by omega)
          · -- n <= 2257906432063
            exact RamareSaouter2003.prime_interval_nat_ladder_c02232 n (by omega) (by omega)
      · -- n <= 2252202710621
        rcases Nat.lt_or_ge 2235177380441 n with h8 | h8
        · -- n > 2235177380441
          rcases Nat.lt_or_ge 2240838220429 n with h10 | h10
          · -- n > 2240838220429
            rcases Nat.lt_or_ge 2246513318677 n with h12 | h12
            · -- n > 2246513318677
              exact RamareSaouter2003.prime_interval_nat_ladder_c02231 n (by omega) (by omega)
            · -- n <= 2246513318677
              exact RamareSaouter2003.prime_interval_nat_ladder_c02230 n (by omega) (by omega)
          · -- n <= 2240838220429
            exact RamareSaouter2003.prime_interval_nat_ladder_c02229 n (by omega) (by omega)
        · -- n <= 2235177380441
          rcases Nat.lt_or_ge 2223898331819 n with h10 | h10
          · -- n > 2223898331819
            rcases Nat.lt_or_ge 2229530762717 n with h12 | h12
            · -- n > 2229530762717
              exact RamareSaouter2003.prime_interval_nat_ladder_c02228 n (by omega) (by omega)
            · -- n <= 2229530762717
              exact RamareSaouter2003.prime_interval_nat_ladder_c02227 n (by omega) (by omega)
          · -- n <= 2223898331819
            exact RamareSaouter2003.prime_interval_nat_ladder_c02226 n (by omega) (by omega)
  · -- n <= 2218280052337
    rcases Nat.lt_or_ge 2146514230279 n with h4 | h4
    · -- n > 2146514230279
      rcases Nat.lt_or_ge 2179345377019 n with h6 | h6
      · -- n > 2179345377019
        rcases Nat.lt_or_ge 2195947742909 n with h8 | h8
        · -- n > 2195947742909
          rcases Nat.lt_or_ge 2207085806407 n with h10 | h10
          · -- n > 2207085806407
            rcases Nat.lt_or_ge 2212675888919 n with h12 | h12
            · -- n > 2212675888919
              exact RamareSaouter2003.prime_interval_nat_ladder_c02225 n (by omega) (by omega)
            · -- n <= 2212675888919
              exact RamareSaouter2003.prime_interval_nat_ladder_c02224 n (by omega) (by omega)
          · -- n <= 2207085806407
            rcases Nat.lt_or_ge 2201509769401 n with h12 | h12
            · -- n > 2201509769401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02223 n (by omega) (by omega)
            · -- n <= 2201509769401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02222 n (by omega) (by omega)
        · -- n <= 2195947742909
          rcases Nat.lt_or_ge 2184865581553 n with h10 | h10
          · -- n > 2184865581553
            rcases Nat.lt_or_ge 2190399691943 n with h12 | h12
            · -- n > 2190399691943
              exact RamareSaouter2003.prime_interval_nat_ladder_c02221 n (by omega) (by omega)
            · -- n <= 2190399691943
              exact RamareSaouter2003.prime_interval_nat_ladder_c02220 n (by omega) (by omega)
          · -- n <= 2184865581553
            exact RamareSaouter2003.prime_interval_nat_ladder_c02219 n (by omega) (by omega)
      · -- n <= 2179345377019
        rcases Nat.lt_or_ge 2162867850643 n with h8 | h8
        · -- n > 2162867850643
          rcases Nat.lt_or_ge 2168346546143 n with h10 | h10
          · -- n > 2168346546143
            rcases Nat.lt_or_ge 2173839043433 n with h12 | h12
            · -- n > 2173839043433
              exact RamareSaouter2003.prime_interval_nat_ladder_c02218 n (by omega) (by omega)
            · -- n <= 2173839043433
              exact RamareSaouter2003.prime_interval_nat_ladder_c02217 n (by omega) (by omega)
          · -- n <= 2168346546143
            exact RamareSaouter2003.prime_interval_nat_ladder_c02216 n (by omega) (by omega)
        · -- n <= 2162867850643
          rcases Nat.lt_or_ge 2151951727069 n with h10 | h10
          · -- n > 2151951727069
            rcases Nat.lt_or_ge 2157402922459 n with h12 | h12
            · -- n > 2157402922459
              exact RamareSaouter2003.prime_interval_nat_ladder_c02215 n (by omega) (by omega)
            · -- n <= 2157402922459
              exact RamareSaouter2003.prime_interval_nat_ladder_c02214 n (by omega) (by omega)
          · -- n <= 2151951727069
            exact RamareSaouter2003.prime_interval_nat_ladder_c02213 n (by omega) (by omega)
    · -- n <= 2146514230279
      rcases Nat.lt_or_ge 2114175007969 n with h6 | h6
      · -- n > 2114175007969
        rcases Nat.lt_or_ge 2130283589209 n with h8 | h8
        · -- n > 2130283589209
          rcases Nat.lt_or_ge 2135680195421 n with h10 | h10
          · -- n > 2135680195421
            rcases Nat.lt_or_ge 2141090397769 n with h12 | h12
            · -- n > 2141090397769
              exact RamareSaouter2003.prime_interval_nat_ladder_c02212 n (by omega) (by omega)
            · -- n <= 2141090397769
              exact RamareSaouter2003.prime_interval_nat_ladder_c02211 n (by omega) (by omega)
          · -- n <= 2135680195421
            exact RamareSaouter2003.prime_interval_nat_ladder_c02210 n (by omega) (by omega)
        · -- n <= 2130283589209
          rcases Nat.lt_or_ge 2119531029367 n with h10 | h10
          · -- n > 2119531029367
            rcases Nat.lt_or_ge 2124900545179 n with h12 | h12
            · -- n > 2124900545179
              exact RamareSaouter2003.prime_interval_nat_ladder_c02209 n (by omega) (by omega)
            · -- n <= 2124900545179
              exact RamareSaouter2003.prime_interval_nat_ladder_c02208 n (by omega) (by omega)
          · -- n <= 2119531029367
            exact RamareSaouter2003.prime_interval_nat_ladder_c02207 n (by omega) (by omega)
      · -- n <= 2114175007969
        rcases Nat.lt_or_ge 2098187573597 n with h8 | h8
        · -- n > 2098187573597
          rcases Nat.lt_or_ge 2103503313673 n with h10 | h10
          · -- n > 2103503313673
            rcases Nat.lt_or_ge 2108832447343 n with h12 | h12
            · -- n > 2108832447343
              exact RamareSaouter2003.prime_interval_nat_ladder_c02206 n (by omega) (by omega)
            · -- n <= 2108832447343
              exact RamareSaouter2003.prime_interval_nat_ladder_c02205 n (by omega) (by omega)
          · -- n <= 2103503313673
            exact RamareSaouter2003.prime_interval_nat_ladder_c02204 n (by omega) (by omega)
        · -- n <= 2098187573597
          rcases Nat.lt_or_ge 2087596139971 n with h10 | h10
          · -- n > 2087596139971
            rcases Nat.lt_or_ge 2092885193411 n with h12 | h12
            · -- n > 2092885193411
              exact RamareSaouter2003.prime_interval_nat_ladder_c02203 n (by omega) (by omega)
            · -- n <= 2092885193411
              exact RamareSaouter2003.prime_interval_nat_ladder_c02202 n (by omega) (by omega)
          · -- n <= 2087596139971
            exact RamareSaouter2003.prime_interval_nat_ladder_c02201 n (by omega) (by omega)
