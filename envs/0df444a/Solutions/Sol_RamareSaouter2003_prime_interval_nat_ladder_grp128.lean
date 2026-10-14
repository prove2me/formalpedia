-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T22:49:46.375537+00:00
-- url     : https://prove2.me/submissions/dbca0f40-5b65-465e-85db-b3ce12d97e56

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06400

theorem solution (n : Nat)
    (hn : 141430315807842023 < n) (hupper : n <= 162905024672217103) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 151788379602625849 n with h2 | h2
  · -- n > 151788379602625849
    rcases Nat.lt_or_ge 157026354408775069 n with h4 | h4
    · -- n > 157026354408775069
      rcases Nat.lt_or_ge 159712741468885859 n with h6 | h6
      · -- n > 159712741468885859
        rcases Nat.lt_or_ge 161073124038194723 n with h8 | h8
        · -- n > 161073124038194723
          rcases Nat.lt_or_ge 161986496888823577 n with h10 | h10
          · -- n > 161986496888823577
            rcases Nat.lt_or_ge 162445129481593247 n with h12 | h12
            · -- n > 162445129481593247
              exact RamareSaouter2003.prime_interval_nat_ladder_c06400 n (by omega) (by omega)
            · -- n <= 162445129481593247
              exact RamareSaouter2003.prime_interval_nat_ladder_c06399 n (by omega) (by omega)
          · -- n <= 161986496888823577
            rcases Nat.lt_or_ge 161529159724096819 n with h12 | h12
            · -- n > 161529159724096819
              exact RamareSaouter2003.prime_interval_nat_ladder_c06398 n (by omega) (by omega)
            · -- n <= 161529159724096819
              exact RamareSaouter2003.prime_interval_nat_ladder_c06397 n (by omega) (by omega)
        · -- n <= 161073124038194723
          rcases Nat.lt_or_ge 160164910056824609 n with h10 | h10
          · -- n > 160164910056824609
            rcases Nat.lt_or_ge 160618383081882223 n with h12 | h12
            · -- n > 160618383081882223
              exact RamareSaouter2003.prime_interval_nat_ladder_c06396 n (by omega) (by omega)
            · -- n <= 160618383081882223
              exact RamareSaouter2003.prime_interval_nat_ladder_c06395 n (by omega) (by omega)
          · -- n <= 160164910056824609
            exact RamareSaouter2003.prime_interval_nat_ladder_c06394 n (by omega) (by omega)
      · -- n <= 159712741468885859
        rcases Nat.lt_or_ge 158363855306283191 n with h8 | h8
        · -- n > 158363855306283191
          rcases Nat.lt_or_ge 158812229967882457 n with h10 | h10
          · -- n > 158812229967882457
            rcases Nat.lt_or_ge 159261873796074481 n with h12 | h12
            · -- n > 159261873796074481
              exact RamareSaouter2003.prime_interval_nat_ladder_c06393 n (by omega) (by omega)
            · -- n <= 159261873796074481
              exact RamareSaouter2003.prime_interval_nat_ladder_c06392 n (by omega) (by omega)
          · -- n <= 158812229967882457
            exact RamareSaouter2003.prime_interval_nat_ladder_c06391 n (by omega) (by omega)
        · -- n <= 158363855306283191
          rcases Nat.lt_or_ge 157470938489606099 n with h10 | h10
          · -- n > 157470938489606099
            rcases Nat.lt_or_ge 157916771744336537 n with h12 | h12
            · -- n > 157916771744336537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06390 n (by omega) (by omega)
            · -- n <= 157916771744336537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06389 n (by omega) (by omega)
          · -- n <= 157470938489606099
            exact RamareSaouter2003.prime_interval_nat_ladder_c06388 n (by omega) (by omega)
    · -- n <= 157026354408775069
      rcases Nat.lt_or_ge 154385139611323337 n with h6 | h6
      · -- n > 154385139611323337
        rcases Nat.lt_or_ge 155700140528222891 n with h8 | h8
        · -- n > 155700140528222891
          rcases Nat.lt_or_ge 156140973116877647 n with h10 | h10
          · -- n > 156140973116877647
            rcases Nat.lt_or_ge 156583035839711161 n with h12 | h12
            · -- n > 156583035839711161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06387 n (by omega) (by omega)
            · -- n <= 156583035839711161
              exact RamareSaouter2003.prime_interval_nat_ladder_c06386 n (by omega) (by omega)
          · -- n <= 156140973116877647
            exact RamareSaouter2003.prime_interval_nat_ladder_c06385 n (by omega) (by omega)
        · -- n <= 155700140528222891
          rcases Nat.lt_or_ge 154822231994872367 n with h10 | h10
          · -- n > 154822231994872367
            rcases Nat.lt_or_ge 155260572595695251 n with h12 | h12
            · -- n > 155260572595695251
              exact RamareSaouter2003.prime_interval_nat_ladder_c06384 n (by omega) (by omega)
            · -- n <= 155260572595695251
              exact RamareSaouter2003.prime_interval_nat_ladder_c06383 n (by omega) (by omega)
          · -- n <= 154822231994872367
            exact RamareSaouter2003.prime_interval_nat_ladder_c06382 n (by omega) (by omega)
      · -- n <= 154385139611323337
        rcases Nat.lt_or_ge 153081278374490339 n with h8 | h8
        · -- n > 153081278374490339
          rcases Nat.lt_or_ge 153514674538060027 n with h10 | h10
          · -- n > 153514674538060027
            rcases Nat.lt_or_ge 153949319764434167 n with h12 | h12
            · -- n > 153949319764434167
              exact RamareSaouter2003.prime_interval_nat_ladder_c06381 n (by omega) (by omega)
            · -- n <= 153949319764434167
              exact RamareSaouter2003.prime_interval_nat_ladder_c06380 n (by omega) (by omega)
          · -- n <= 153514674538060027
            exact RamareSaouter2003.prime_interval_nat_ladder_c06379 n (by omega) (by omega)
        · -- n <= 153081278374490339
          rcases Nat.lt_or_ge 152218115513565589 n with h10 | h10
          · -- n > 152218115513565589
            rcases Nat.lt_or_ge 152649090270121363 n with h12 | h12
            · -- n > 152649090270121363
              exact RamareSaouter2003.prime_interval_nat_ladder_c06378 n (by omega) (by omega)
            · -- n <= 152649090270121363
              exact RamareSaouter2003.prime_interval_nat_ladder_c06377 n (by omega) (by omega)
          · -- n <= 152218115513565589
            exact RamareSaouter2003.prime_interval_nat_ladder_c06376 n (by omega) (by omega)
  · -- n <= 151788379602625849
    rcases Nat.lt_or_ge 146310856631792471 n with h4 | h4
    · -- n > 146310856631792471
      rcases Nat.lt_or_ge 148813935683244631 n with h6 | h6
      · -- n > 148813935683244631
        rcases Nat.lt_or_ge 150081473420122351 n with h8 | h8
        · -- n > 150081473420122351
          rcases Nat.lt_or_ge 150932514934420039 n with h10 | h10
          · -- n > 150932514934420039
            rcases Nat.lt_or_ge 151359838582197653 n with h12 | h12
            · -- n > 151359838582197653
              exact RamareSaouter2003.prime_interval_nat_ladder_c06375 n (by omega) (by omega)
            · -- n <= 151359838582197653
              exact RamareSaouter2003.prime_interval_nat_ladder_c06374 n (by omega) (by omega)
          · -- n <= 150932514934420039
            rcases Nat.lt_or_ge 150506394305470351 n with h12 | h12
            · -- n > 150506394305470351
              exact RamareSaouter2003.prime_interval_nat_ladder_c06373 n (by omega) (by omega)
            · -- n <= 150506394305470351
              exact RamareSaouter2003.prime_interval_nat_ladder_c06372 n (by omega) (by omega)
        · -- n <= 150081473420122351
          rcases Nat.lt_or_ge 149235269492665883 n with h10 | h10
          · -- n > 149235269492665883
            rcases Nat.lt_or_ge 149657796193806067 n with h12 | h12
            · -- n > 149657796193806067
              exact RamareSaouter2003.prime_interval_nat_ladder_c06371 n (by omega) (by omega)
            · -- n <= 149657796193806067
              exact RamareSaouter2003.prime_interval_nat_ladder_c06370 n (by omega) (by omega)
          · -- n <= 149235269492665883
            exact RamareSaouter2003.prime_interval_nat_ladder_c06369 n (by omega) (by omega)
      · -- n <= 148813935683244631
        rcases Nat.lt_or_ge 147557103414624529 n with h8 | h8
        · -- n > 147557103414624529
          rcases Nat.lt_or_ge 147974848268570927 n with h10 | h10
          · -- n > 147974848268570927
            rcases Nat.lt_or_ge 148393797658310593 n with h12 | h12
            · -- n > 148393797658310593
              exact RamareSaouter2003.prime_interval_nat_ladder_c06368 n (by omega) (by omega)
            · -- n <= 148393797658310593
              exact RamareSaouter2003.prime_interval_nat_ladder_c06367 n (by omega) (by omega)
          · -- n <= 147974848268570927
            exact RamareSaouter2003.prime_interval_nat_ladder_c06366 n (by omega) (by omega)
        · -- n <= 147557103414624529
          rcases Nat.lt_or_ge 146725106602182893 n with h10 | h10
          · -- n > 146725106602182893
            rcases Nat.lt_or_ge 147140515996386763 n with h12 | h12
            · -- n > 147140515996386763
              exact RamareSaouter2003.prime_interval_nat_ladder_c06365 n (by omega) (by omega)
            · -- n <= 147140515996386763
              exact RamareSaouter2003.prime_interval_nat_ladder_c06364 n (by omega) (by omega)
          · -- n <= 146725106602182893
            exact RamareSaouter2003.prime_interval_nat_ladder_c06363 n (by omega) (by omega)
    · -- n <= 146310856631792471
      rcases Nat.lt_or_ge 143849862504596173 n with h6 | h6
      · -- n > 143849862504596173
        rcases Nat.lt_or_ge 145075155772968101 n with h8 | h8
        · -- n > 145075155772968101
          rcases Nat.lt_or_ge 145485897074766917 n with h10 | h10
          · -- n > 145485897074766917
            rcases Nat.lt_or_ge 145897779757051733 n with h12 | h12
            · -- n > 145897779757051733
              exact RamareSaouter2003.prime_interval_nat_ladder_c06362 n (by omega) (by omega)
            · -- n <= 145897779757051733
              exact RamareSaouter2003.prime_interval_nat_ladder_c06361 n (by omega) (by omega)
          · -- n <= 145485897074766917
            exact RamareSaouter2003.prime_interval_nat_ladder_c06360 n (by omega) (by omega)
        · -- n <= 145075155772968101
          rcases Nat.lt_or_ge 144257139433102523 n with h10 | h10
          · -- n > 144257139433102523
            rcases Nat.lt_or_ge 144665572506364529 n with h12 | h12
            · -- n > 144665572506364529
              exact RamareSaouter2003.prime_interval_nat_ladder_c06359 n (by omega) (by omega)
            · -- n <= 144665572506364529
              exact RamareSaouter2003.prime_interval_nat_ladder_c06358 n (by omega) (by omega)
          · -- n <= 144257139433102523
            exact RamareSaouter2003.prime_interval_nat_ladder_c06357 n (by omega) (by omega)
      · -- n <= 143849862504596173
        rcases Nat.lt_or_ge 142634938078616723 n with h8 | h8
        · -- n > 142634938078616723
          rcases Nat.lt_or_ge 143038777147071803 n with h10 | h10
          · -- n > 143038777147071803
            rcases Nat.lt_or_ge 143443752168652927 n with h12 | h12
            · -- n > 143443752168652927
              exact RamareSaouter2003.prime_interval_nat_ladder_c06356 n (by omega) (by omega)
            · -- n <= 143443752168652927
              exact RamareSaouter2003.prime_interval_nat_ladder_c06355 n (by omega) (by omega)
          · -- n <= 143038777147071803
            exact RamareSaouter2003.prime_interval_nat_ladder_c06354 n (by omega) (by omega)
        · -- n <= 142634938078616723
          rcases Nat.lt_or_ge 141830734330037141 n with h10 | h10
          · -- n > 141830734330037141
            rcases Nat.lt_or_ge 142232242365812461 n with h12 | h12
            · -- n > 142232242365812461
              exact RamareSaouter2003.prime_interval_nat_ladder_c06353 n (by omega) (by omega)
            · -- n <= 142232242365812461
              exact RamareSaouter2003.prime_interval_nat_ladder_c06352 n (by omega) (by omega)
          · -- n <= 141830734330037141
            exact RamareSaouter2003.prime_interval_nat_ladder_c06351 n (by omega) (by omega)
