-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T06:16:13.929906+00:00
-- url     : https://prove2.me/submissions/62690d4b-2b77-437c-b3b0-38dec873fca2

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01350

theorem solution (n : Nat)
    (hn : 214261267621 < n) (hupper : n <= 242864356649) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 228110781911 n with h2 | h2
  · -- n > 228110781911
    rcases Nat.lt_or_ge 235076091997 n with h4 | h4
    · -- n > 235076091997
      rcases Nat.lt_or_ge 238638853909 n with h6 | h6
      · -- n > 238638853909
        rcases Nat.lt_or_ge 240440621969 n with h8 | h8
        · -- n > 240440621969
          rcases Nat.lt_or_ge 241649422327 n with h10 | h10
          · -- n > 241649422327
            rcases Nat.lt_or_ge 242256120811 n with h12 | h12
            · -- n > 242256120811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01350 n (by omega) (by omega)
            · -- n <= 242256120811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01349 n (by omega) (by omega)
          · -- n <= 241649422327
            rcases Nat.lt_or_ge 241044257413 n with h12 | h12
            · -- n > 241044257413
              exact RamareSaouter2003.prime_interval_nat_ladder_c01348 n (by omega) (by omega)
            · -- n <= 241044257413
              exact RamareSaouter2003.prime_interval_nat_ladder_c01347 n (by omega) (by omega)
        · -- n <= 240440621969
          rcases Nat.lt_or_ge 239237924089 n with h10 | h10
          · -- n > 239237924089
            rcases Nat.lt_or_ge 239838512161 n with h12 | h12
            · -- n > 239838512161
              exact RamareSaouter2003.prime_interval_nat_ladder_c01346 n (by omega) (by omega)
            · -- n <= 239838512161
              exact RamareSaouter2003.prime_interval_nat_ladder_c01345 n (by omega) (by omega)
          · -- n <= 239237924089
            exact RamareSaouter2003.prime_interval_nat_ladder_c01344 n (by omega) (by omega)
      · -- n <= 238638853909
        rcases Nat.lt_or_ge 236850711931 n with h8 | h8
        · -- n > 236850711931
          rcases Nat.lt_or_ge 237445251661 n with h10 | h10
          · -- n > 237445251661
            rcases Nat.lt_or_ge 238041297727 n with h12 | h12
            · -- n > 238041297727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01343 n (by omega) (by omega)
            · -- n <= 238041297727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01342 n (by omega) (by omega)
          · -- n <= 237445251661
            exact RamareSaouter2003.prime_interval_nat_ladder_c01341 n (by omega) (by omega)
        · -- n <= 236850711931
          rcases Nat.lt_or_ge 235666135889 n with h10 | h10
          · -- n > 235666135889
            rcases Nat.lt_or_ge 236257674599 n with h12 | h12
            · -- n > 236257674599
              exact RamareSaouter2003.prime_interval_nat_ladder_c01340 n (by omega) (by omega)
            · -- n <= 236257674599
              exact RamareSaouter2003.prime_interval_nat_ladder_c01339 n (by omega) (by omega)
          · -- n <= 235666135889
            exact RamareSaouter2003.prime_interval_nat_ladder_c01338 n (by omega) (by omega)
    · -- n <= 235076091997
      rcases Nat.lt_or_ge 231567006641 n with h6 | h6
      · -- n > 231567006641
        rcases Nat.lt_or_ge 233314891009 n with h8 | h8
        · -- n > 233314891009
          rcases Nat.lt_or_ge 233900473361 n with h10 | h10
          · -- n > 233900473361
            rcases Nat.lt_or_ge 234487539079 n with h12 | h12
            · -- n > 234487539079
              exact RamareSaouter2003.prime_interval_nat_ladder_c01337 n (by omega) (by omega)
            · -- n <= 234487539079
              exact RamareSaouter2003.prime_interval_nat_ladder_c01336 n (by omega) (by omega)
          · -- n <= 233900473361
            exact RamareSaouter2003.prime_interval_nat_ladder_c01335 n (by omega) (by omega)
        · -- n <= 233314891009
          rcases Nat.lt_or_ge 232148161409 n with h10 | h10
          · -- n > 232148161409
            rcases Nat.lt_or_ge 232730788271 n with h12 | h12
            · -- n > 232730788271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01334 n (by omega) (by omega)
            · -- n <= 232730788271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01333 n (by omega) (by omega)
          · -- n <= 232148161409
            exact RamareSaouter2003.prime_interval_nat_ladder_c01332 n (by omega) (by omega)
      · -- n <= 231567006641
        rcases Nat.lt_or_ge 229832337167 n with h8 | h8
        · -- n > 229832337167
          rcases Nat.lt_or_ge 230409098243 n with h10 | h10
          · -- n > 230409098243
            rcases Nat.lt_or_ge 230987320171 n with h12 | h12
            · -- n > 230987320171
              exact RamareSaouter2003.prime_interval_nat_ladder_c01331 n (by omega) (by omega)
            · -- n <= 230987320171
              exact RamareSaouter2003.prime_interval_nat_ladder_c01330 n (by omega) (by omega)
          · -- n <= 230409098243
            exact RamareSaouter2003.prime_interval_nat_ladder_c01329 n (by omega) (by omega)
        · -- n <= 229832337167
          rcases Nat.lt_or_ge 228683182709 n with h10 | h10
          · -- n > 228683182709
            rcases Nat.lt_or_ge 229257033211 n with h12 | h12
            · -- n > 229257033211
              exact RamareSaouter2003.prime_interval_nat_ladder_c01328 n (by omega) (by omega)
            · -- n <= 229257033211
              exact RamareSaouter2003.prime_interval_nat_ladder_c01327 n (by omega) (by omega)
          · -- n <= 228683182709
            exact RamareSaouter2003.prime_interval_nat_ladder_c01326 n (by omega) (by omega)
  · -- n <= 228110781911
    rcases Nat.lt_or_ge 220799824691 n with h4 | h4
    · -- n > 220799824691
      rcases Nat.lt_or_ge 224144258209 n with h6 | h6
      · -- n > 224144258209
        rcases Nat.lt_or_ge 225835601729 n with h8 | h8
        · -- n > 225835601729
          rcases Nat.lt_or_ge 226970314553 n with h10 | h10
          · -- n > 226970314553
            rcases Nat.lt_or_ge 227539827029 n with h12 | h12
            · -- n > 227539827029
              exact RamareSaouter2003.prime_interval_nat_ladder_c01325 n (by omega) (by omega)
            · -- n <= 227539827029
              exact RamareSaouter2003.prime_interval_nat_ladder_c01324 n (by omega) (by omega)
          · -- n <= 226970314553
            rcases Nat.lt_or_ge 226402240681 n with h12 | h12
            · -- n > 226402240681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01323 n (by omega) (by omega)
            · -- n <= 226402240681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01322 n (by omega) (by omega)
        · -- n <= 225835601729
          rcases Nat.lt_or_ge 224706614129 n with h10 | h10
          · -- n > 224706614129
            rcases Nat.lt_or_ge 225270394093 n with h12 | h12
            · -- n > 225270394093
              exact RamareSaouter2003.prime_interval_nat_ladder_c01321 n (by omega) (by omega)
            · -- n <= 225270394093
              exact RamareSaouter2003.prime_interval_nat_ladder_c01320 n (by omega) (by omega)
          · -- n <= 224706614129
            exact RamareSaouter2003.prime_interval_nat_ladder_c01319 n (by omega) (by omega)
      · -- n <= 224144258209
        rcases Nat.lt_or_ge 222465698461 n with h8 | h8
        · -- n > 222465698461
          rcases Nat.lt_or_ge 223023804067 n with h10 | h10
          · -- n > 223023804067
            rcases Nat.lt_or_ge 223583322659 n with h12 | h12
            · -- n > 223583322659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01318 n (by omega) (by omega)
            · -- n <= 223583322659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01317 n (by omega) (by omega)
          · -- n <= 223023804067
            exact RamareSaouter2003.prime_interval_nat_ladder_c01316 n (by omega) (by omega)
        · -- n <= 222465698461
          rcases Nat.lt_or_ge 221353712369 n with h10 | h10
          · -- n > 221353712369
            rcases Nat.lt_or_ge 221909002417 n with h12 | h12
            · -- n > 221909002417
              exact RamareSaouter2003.prime_interval_nat_ladder_c01315 n (by omega) (by omega)
            · -- n <= 221909002417
              exact RamareSaouter2003.prime_interval_nat_ladder_c01314 n (by omega) (by omega)
          · -- n <= 221353712369
            exact RamareSaouter2003.prime_interval_nat_ladder_c01313 n (by omega) (by omega)
    · -- n <= 220799824691
      rcases Nat.lt_or_ge 217505749693 n with h6 | h6
      · -- n > 217505749693
        rcases Nat.lt_or_ge 219146540527 n with h8 | h8
        · -- n > 219146540527
          rcases Nat.lt_or_ge 219696242407 n with h10 | h10
          · -- n > 219696242407
            rcases Nat.lt_or_ge 220247335927 n with h12 | h12
            · -- n > 220247335927
              exact RamareSaouter2003.prime_interval_nat_ladder_c01312 n (by omega) (by omega)
            · -- n <= 220247335927
              exact RamareSaouter2003.prime_interval_nat_ladder_c01311 n (by omega) (by omega)
          · -- n <= 219696242407
            exact RamareSaouter2003.prime_interval_nat_ladder_c01310 n (by omega) (by omega)
        · -- n <= 219146540527
          rcases Nat.lt_or_ge 218051297707 n with h10 | h10
          · -- n > 218051297707
            rcases Nat.lt_or_ge 218598226837 n with h12 | h12
            · -- n > 218598226837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01309 n (by omega) (by omega)
            · -- n <= 218598226837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01308 n (by omega) (by omega)
          · -- n <= 218051297707
            exact RamareSaouter2003.prime_interval_nat_ladder_c01307 n (by omega) (by omega)
      · -- n <= 217505749693
        rcases Nat.lt_or_ge 215877356857 n with h8 | h8
        · -- n > 215877356857
          rcases Nat.lt_or_ge 216418782751 n with h10 | h10
          · -- n > 216418782751
            rcases Nat.lt_or_ge 216961579183 n with h12 | h12
            · -- n > 216961579183
              exact RamareSaouter2003.prime_interval_nat_ladder_c01306 n (by omega) (by omega)
            · -- n <= 216961579183
              exact RamareSaouter2003.prime_interval_nat_ladder_c01305 n (by omega) (by omega)
          · -- n <= 216418782751
            exact RamareSaouter2003.prime_interval_nat_ladder_c01304 n (by omega) (by omega)
        · -- n <= 215877356857
          rcases Nat.lt_or_ge 214798602769 n with h10 | h10
          · -- n > 214798602769
            rcases Nat.lt_or_ge 215337298039 n with h12 | h12
            · -- n > 215337298039
              exact RamareSaouter2003.prime_interval_nat_ladder_c01303 n (by omega) (by omega)
            · -- n <= 215337298039
              exact RamareSaouter2003.prime_interval_nat_ladder_c01302 n (by omega) (by omega)
          · -- n <= 214798602769
            exact RamareSaouter2003.prime_interval_nat_ladder_c01301 n (by omega) (by omega)
