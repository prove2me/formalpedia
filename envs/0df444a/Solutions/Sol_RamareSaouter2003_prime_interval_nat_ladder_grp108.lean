-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T16:17:10.721576+00:00
-- url     : https://prove2.me/submissions/9fce6a71-43a2-41e7-9659-0f13e1cd31cf

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05400

theorem solution (n : Nat)
    (hn : 8370471890560501 < n) (hupper : n <= 9641307945289051) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 8983462157826649 n with h2 | h2
  · -- n > 8983462157826649
    rcases Nat.lt_or_ge 9293431098801211 n with h4 | h4
    · -- n > 9293431098801211
      rcases Nat.lt_or_ge 9452398707454421 n with h6 | h6
      · -- n > 9452398707454421
        rcases Nat.lt_or_ge 9532901419070251 n with h8 | h8
        · -- n > 9532901419070251
          rcases Nat.lt_or_ge 9586955230000571 n with h10 | h10
          · -- n > 9586955230000571
            rcases Nat.lt_or_ge 9614096497655623 n with h12 | h12
            · -- n > 9614096497655623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05400 n (by omega) (by omega)
            · -- n <= 9614096497655623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05399 n (by omega) (by omega)
          · -- n <= 9586955230000571
            rcases Nat.lt_or_ge 9559889275507003 n with h12 | h12
            · -- n > 9559889275507003
              exact RamareSaouter2003.prime_interval_nat_ladder_c05398 n (by omega) (by omega)
            · -- n <= 9559889275507003
              exact RamareSaouter2003.prime_interval_nat_ladder_c05397 n (by omega) (by omega)
        · -- n <= 9532901419070251
          rcases Nat.lt_or_ge 9479159321098853 n with h10 | h10
          · -- n > 9479159321098853
            rcases Nat.lt_or_ge 9505994417477351 n with h12 | h12
            · -- n > 9505994417477351
              exact RamareSaouter2003.prime_interval_nat_ladder_c05396 n (by omega) (by omega)
            · -- n <= 9505994417477351
              exact RamareSaouter2003.prime_interval_nat_ladder_c05395 n (by omega) (by omega)
          · -- n <= 9479159321098853
            exact RamareSaouter2003.prime_interval_nat_ladder_c05394 n (by omega) (by omega)
      · -- n <= 9452398707454421
        rcases Nat.lt_or_ge 9372576779720981 n with h8 | h8
        · -- n > 9372576779720981
          rcases Nat.lt_or_ge 9399109450346221 n with h10 | h10
          · -- n > 9399109450346221
            rcases Nat.lt_or_ge 9425718068459129 n with h12 | h12
            · -- n > 9425718068459129
              exact RamareSaouter2003.prime_interval_nat_ladder_c05393 n (by omega) (by omega)
            · -- n <= 9425718068459129
              exact RamareSaouter2003.prime_interval_nat_ladder_c05392 n (by omega) (by omega)
          · -- n <= 9399109450346221
            exact RamareSaouter2003.prime_interval_nat_ladder_c05391 n (by omega) (by omega)
        · -- n <= 9372576779720981
          rcases Nat.lt_or_ge 9319737090870197 n with h10 | h10
          · -- n > 9319737090870197
            rcases Nat.lt_or_ge 9346119895842589 n with h12 | h12
            · -- n > 9346119895842589
              exact RamareSaouter2003.prime_interval_nat_ladder_c05390 n (by omega) (by omega)
            · -- n <= 9346119895842589
              exact RamareSaouter2003.prime_interval_nat_ladder_c05389 n (by omega) (by omega)
          · -- n <= 9319737090870197
            exact RamareSaouter2003.prime_interval_nat_ladder_c05388 n (by omega) (by omega)
    · -- n <= 9293431098801211
      rcases Nat.lt_or_ge 9137126833205603 n with h6 | h6
      · -- n > 9137126833205603
        rcases Nat.lt_or_ge 9214940862155519 n with h8 | h8
        · -- n > 9214940862155519
          rcases Nat.lt_or_ge 9241030250214949 n with h10 | h10
          · -- n > 9241030250214949
            rcases Nat.lt_or_ge 9267194444182049 n with h12 | h12
            · -- n > 9267194444182049
              exact RamareSaouter2003.prime_interval_nat_ladder_c05387 n (by omega) (by omega)
            · -- n <= 9267194444182049
              exact RamareSaouter2003.prime_interval_nat_ladder_c05386 n (by omega) (by omega)
          · -- n <= 9241030250214949
            exact RamareSaouter2003.prime_interval_nat_ladder_c05385 n (by omega) (by omega)
        · -- n <= 9214940862155519
          rcases Nat.lt_or_ge 9162995059504921 n with h10 | h10
          · -- n > 9162995059504921
            rcases Nat.lt_or_ge 9188927077806041 n with h12 | h12
            · -- n > 9188927077806041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05384 n (by omega) (by omega)
            · -- n <= 9188927077806041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05383 n (by omega) (by omega)
          · -- n <= 9162995059504921
            exact RamareSaouter2003.prime_interval_nat_ladder_c05382 n (by omega) (by omega)
      · -- n <= 9137126833205603
        rcases Nat.lt_or_ge 9059969409953323 n with h8 | h8
        · -- n > 9059969409953323
          rcases Nat.lt_or_ge 9085619223561053 n with h10 | h10
          · -- n > 9085619223561053
            rcases Nat.lt_or_ge 9111336786294569 n with h12 | h12
            · -- n > 9111336786294569
              exact RamareSaouter2003.prime_interval_nat_ladder_c05381 n (by omega) (by omega)
            · -- n <= 9111336786294569
              exact RamareSaouter2003.prime_interval_nat_ladder_c05380 n (by omega) (by omega)
          · -- n <= 9085619223561053
            exact RamareSaouter2003.prime_interval_nat_ladder_c05379 n (by omega) (by omega)
        · -- n <= 9059969409953323
          rcases Nat.lt_or_ge 9008892270906083 n with h10 | h10
          · -- n > 9008892270906083
            rcases Nat.lt_or_ge 9034390643492881 n with h12 | h12
            · -- n > 9034390643492881
              exact RamareSaouter2003.prime_interval_nat_ladder_c05378 n (by omega) (by omega)
            · -- n <= 9034390643492881
              exact RamareSaouter2003.prime_interval_nat_ladder_c05377 n (by omega) (by omega)
          · -- n <= 9008892270906083
            exact RamareSaouter2003.prime_interval_nat_ladder_c05376 n (by omega) (by omega)
  · -- n <= 8983462157826649
    rcases Nat.lt_or_ge 8659304835537217 n with h4 | h4
    · -- n > 8659304835537217
      rcases Nat.lt_or_ge 8807441617411607 n with h6 | h6
      · -- n > 8807441617411607
        rcases Nat.lt_or_ge 8882457183391289 n with h8 | h8
        · -- n > 8882457183391289
          rcases Nat.lt_or_ge 8932815799538123 n with h10 | h10
          · -- n > 8932815799538123
            rcases Nat.lt_or_ge 8958102436399379 n with h12 | h12
            · -- n > 8958102436399379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05375 n (by omega) (by omega)
            · -- n <= 8958102436399379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05374 n (by omega) (by omega)
          · -- n <= 8932815799538123
            rcases Nat.lt_or_ge 8907600387462113 n with h12 | h12
            · -- n > 8907600387462113
              exact RamareSaouter2003.prime_interval_nat_ladder_c05373 n (by omega) (by omega)
            · -- n <= 8907600387462113
              exact RamareSaouter2003.prime_interval_nat_ladder_c05372 n (by omega) (by omega)
        · -- n <= 8882457183391289
          rcases Nat.lt_or_ge 8832376431841891 n with h10 | h10
          · -- n > 8832376431841891
            rcases Nat.lt_or_ge 8857382265357671 n with h12 | h12
            · -- n > 8857382265357671
              exact RamareSaouter2003.prime_interval_nat_ladder_c05371 n (by omega) (by omega)
            · -- n <= 8857382265357671
              exact RamareSaouter2003.prime_interval_nat_ladder_c05370 n (by omega) (by omega)
          · -- n <= 8832376431841891
            exact RamareSaouter2003.prime_interval_nat_ladder_c05369 n (by omega) (by omega)
      · -- n <= 8807441617411607
        rcases Nat.lt_or_ge 8733058522028507 n with h8 | h8
        · -- n > 8733058522028507
          rcases Nat.lt_or_ge 8757783840904073 n with h10 | h10
          · -- n > 8757783840904073
            rcases Nat.lt_or_ge 8782575969277051 n with h12 | h12
            · -- n > 8782575969277051
              exact RamareSaouter2003.prime_interval_nat_ladder_c05368 n (by omega) (by omega)
            · -- n <= 8782575969277051
              exact RamareSaouter2003.prime_interval_nat_ladder_c05367 n (by omega) (by omega)
          · -- n <= 8757783840904073
            exact RamareSaouter2003.prime_interval_nat_ladder_c05366 n (by omega) (by omega)
        · -- n <= 8733058522028507
          rcases Nat.lt_or_ge 8683818618992731 n with h10 | h10
          · -- n > 8683818618992731
            rcases Nat.lt_or_ge 8708404185163477 n with h12 | h12
            · -- n > 8708404185163477
              exact RamareSaouter2003.prime_interval_nat_ladder_c05365 n (by omega) (by omega)
            · -- n <= 8708404185163477
              exact RamareSaouter2003.prime_interval_nat_ladder_c05364 n (by omega) (by omega)
          · -- n <= 8683818618992731
            exact RamareSaouter2003.prime_interval_nat_ladder_c05363 n (by omega) (by omega)
    · -- n <= 8659304835537217
      rcases Nat.lt_or_ge 8513660621195243 n with h6 | h6
      · -- n > 8513660621195243
        rcases Nat.lt_or_ge 8586176732898833 n with h8 | h8
        · -- n > 8586176732898833
          rcases Nat.lt_or_ge 8610485894722589 n with h10 | h10
          · -- n > 8610485894722589
            rcases Nat.lt_or_ge 8634862320847673 n with h12 | h12
            · -- n > 8634862320847673
              exact RamareSaouter2003.prime_interval_nat_ladder_c05362 n (by omega) (by omega)
            · -- n <= 8634862320847673
              exact RamareSaouter2003.prime_interval_nat_ladder_c05361 n (by omega) (by omega)
          · -- n <= 8610485894722589
            exact RamareSaouter2003.prime_interval_nat_ladder_c05360 n (by omega) (by omega)
        · -- n <= 8586176732898833
          rcases Nat.lt_or_ge 8537764982162903 n with h10 | h10
          · -- n > 8537764982162903
            rcases Nat.lt_or_ge 8561938009847407 n with h12 | h12
            · -- n > 8561938009847407
              exact RamareSaouter2003.prime_interval_nat_ladder_c05359 n (by omega) (by omega)
            · -- n <= 8561938009847407
              exact RamareSaouter2003.prime_interval_nat_ladder_c05358 n (by omega) (by omega)
          · -- n <= 8537764982162903
            exact RamareSaouter2003.prime_interval_nat_ladder_c05357 n (by omega) (by omega)
      · -- n <= 8513660621195243
        rcases Nat.lt_or_ge 8441762587411991 n with h8 | h8
        · -- n > 8441762587411991
          rcases Nat.lt_or_ge 8465661785720807 n with h10 | h10
          · -- n > 8465661785720807
            rcases Nat.lt_or_ge 8489629223882579 n with h12 | h12
            · -- n > 8489629223882579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05356 n (by omega) (by omega)
            · -- n <= 8489629223882579
              exact RamareSaouter2003.prime_interval_nat_ladder_c05355 n (by omega) (by omega)
          · -- n <= 8465661785720807
            exact RamareSaouter2003.prime_interval_nat_ladder_c05354 n (by omega) (by omega)
        · -- n <= 8441762587411991
          rcases Nat.lt_or_ge 8394167236860439 n with h10 | h10
          · -- n > 8394167236860439
            rcases Nat.lt_or_ge 8417931851976601 n with h12 | h12
            · -- n > 8417931851976601
              exact RamareSaouter2003.prime_interval_nat_ladder_c05353 n (by omega) (by omega)
            · -- n <= 8417931851976601
              exact RamareSaouter2003.prime_interval_nat_ladder_c05352 n (by omega) (by omega)
          · -- n <= 8394167236860439
            exact RamareSaouter2003.prime_interval_nat_ladder_c05351 n (by omega) (by omega)
