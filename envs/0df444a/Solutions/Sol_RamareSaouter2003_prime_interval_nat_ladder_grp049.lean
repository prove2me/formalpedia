-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T21:33:15.625123+00:00
-- url     : https://prove2.me/submissions/31ac8b2e-5be8-4e3a-aa72-a9ca594e232d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02450

theorem solution (n : Nat)
    (hn : 3443870585447 < n) (hupper : n <= 3896894525047) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3663386469889 n with h2 | h2
  · -- n > 3663386469889
    rcases Nat.lt_or_ge 3773670491291 n with h4 | h4
    · -- n > 3773670491291
      rcases Nat.lt_or_ge 3830051337419 n with h6 | h6
      · -- n > 3830051337419
        rcases Nat.lt_or_ge 3858556864207 n with h8 | h8
        · -- n > 3858556864207
          rcases Nat.lt_or_ge 3877678315507 n with h10 | h10
          · -- n > 3877678315507
            rcases Nat.lt_or_ge 3887274546241 n with h12 | h12
            · -- n > 3887274546241
              exact RamareSaouter2003.prime_interval_nat_ladder_c02450 n (by omega) (by omega)
            · -- n <= 3887274546241
              exact RamareSaouter2003.prime_interval_nat_ladder_c02449 n (by omega) (by omega)
          · -- n <= 3877678315507
            rcases Nat.lt_or_ge 3868105774399 n with h12 | h12
            · -- n > 3868105774399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02448 n (by omega) (by omega)
            · -- n <= 3868105774399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02447 n (by omega) (by omega)
        · -- n <= 3858556864207
          rcases Nat.lt_or_ge 3839529703907 n with h10 | h10
          · -- n > 3839529703907
            rcases Nat.lt_or_ge 3849031526797 n with h12 | h12
            · -- n > 3849031526797
              exact RamareSaouter2003.prime_interval_nat_ladder_c02446 n (by omega) (by omega)
            · -- n <= 3849031526797
              exact RamareSaouter2003.prime_interval_nat_ladder_c02445 n (by omega) (by omega)
          · -- n <= 3839529703907
            exact RamareSaouter2003.prime_interval_nat_ladder_c02444 n (by omega) (by omega)
      · -- n <= 3830051337419
        rcases Nat.lt_or_ge 3801756398357 n with h8 | h8
        · -- n > 3801756398357
          rcases Nat.lt_or_ge 3811164742351 n with h10 | h10
          · -- n > 3811164742351
            rcases Nat.lt_or_ge 3820596369431 n with h12 | h12
            · -- n > 3820596369431
              exact RamareSaouter2003.prime_interval_nat_ladder_c02443 n (by omega) (by omega)
            · -- n <= 3820596369431
              exact RamareSaouter2003.prime_interval_nat_ladder_c02442 n (by omega) (by omega)
          · -- n <= 3811164742351
            exact RamareSaouter2003.prime_interval_nat_ladder_c02441 n (by omega) (by omega)
        · -- n <= 3801756398357
          rcases Nat.lt_or_ge 3783009330097 n with h10 | h10
          · -- n > 3783009330097
            rcases Nat.lt_or_ge 3792371280017 n with h12 | h12
            · -- n > 3792371280017
              exact RamareSaouter2003.prime_interval_nat_ladder_c02440 n (by omega) (by omega)
            · -- n <= 3792371280017
              exact RamareSaouter2003.prime_interval_nat_ladder_c02439 n (by omega) (by omega)
          · -- n <= 3783009330097
            exact RamareSaouter2003.prime_interval_nat_ladder_c02438 n (by omega) (by omega)
    · -- n <= 3773670491291
      rcases Nat.lt_or_ge 3718119608089 n with h6 | h6
      · -- n > 3718119608089
        rcases Nat.lt_or_ge 3745792072219 n with h8 | h8
        · -- n > 3745792072219
          rcases Nat.lt_or_ge 3755061919153 n with h10 | h10
          · -- n > 3755061919153
            rcases Nat.lt_or_ge 3764354706641 n with h12 | h12
            · -- n > 3764354706641
              exact RamareSaouter2003.prime_interval_nat_ladder_c02437 n (by omega) (by omega)
            · -- n <= 3764354706641
              exact RamareSaouter2003.prime_interval_nat_ladder_c02436 n (by omega) (by omega)
          · -- n <= 3755061919153
            exact RamareSaouter2003.prime_interval_nat_ladder_c02435 n (by omega) (by omega)
        · -- n <= 3745792072219
          rcases Nat.lt_or_ge 3727320973133 n with h10 | h10
          · -- n > 3727320973133
            rcases Nat.lt_or_ge 3736545109027 n with h12 | h12
            · -- n > 3736545109027
              exact RamareSaouter2003.prime_interval_nat_ladder_c02434 n (by omega) (by omega)
            · -- n <= 3736545109027
              exact RamareSaouter2003.prime_interval_nat_ladder_c02433 n (by omega) (by omega)
          · -- n <= 3727320973133
            exact RamareSaouter2003.prime_interval_nat_ladder_c02432 n (by omega) (by omega)
      · -- n <= 3718119608089
        rcases Nat.lt_or_ge 3690651577271 n with h8 | h8
        · -- n > 3690651577271
          rcases Nat.lt_or_ge 3699784966177 n with h10 | h10
          · -- n > 3699784966177
            rcases Nat.lt_or_ge 3708940957811 n with h12 | h12
            · -- n > 3708940957811
              exact RamareSaouter2003.prime_interval_nat_ladder_c02431 n (by omega) (by omega)
            · -- n <= 3708940957811
              exact RamareSaouter2003.prime_interval_nat_ladder_c02430 n (by omega) (by omega)
          · -- n <= 3699784966177
            exact RamareSaouter2003.prime_interval_nat_ladder_c02429 n (by omega) (by omega)
        · -- n <= 3690651577271
          rcases Nat.lt_or_ge 3672452384767 n with h10 | h10
          · -- n > 3672452384767
            rcases Nat.lt_or_ge 3681540735373 n with h12 | h12
            · -- n > 3681540735373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02428 n (by omega) (by omega)
            · -- n <= 3681540735373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02427 n (by omega) (by omega)
          · -- n <= 3672452384767
            exact RamareSaouter2003.prime_interval_nat_ladder_c02426 n (by omega) (by omega)
  · -- n <= 3663386469889
    rcases Nat.lt_or_ge 3547546214351 n with h4 | h4
    · -- n > 3547546214351
      rcases Nat.lt_or_ge 3600548631187 n with h6 | h6
      · -- n > 3600548631187
        rcases Nat.lt_or_ge 3627346061947 n with h8 | h8
        · -- n > 3627346061947
          rcases Nat.lt_or_ge 3645321725867 n with h10 | h10
          · -- n > 3645321725867
            rcases Nat.lt_or_ge 3654342935359 n with h12 | h12
            · -- n > 3654342935359
              exact RamareSaouter2003.prime_interval_nat_ladder_c02425 n (by omega) (by omega)
            · -- n <= 3654342935359
              exact RamareSaouter2003.prime_interval_nat_ladder_c02424 n (by omega) (by omega)
          · -- n <= 3645321725867
            rcases Nat.lt_or_ge 3636322786373 n with h12 | h12
            · -- n > 3636322786373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02423 n (by omega) (by omega)
            · -- n <= 3636322786373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02422 n (by omega) (by omega)
        · -- n <= 3627346061947
          rcases Nat.lt_or_ge 3609459039073 n with h10 | h10
          · -- n > 3609459039073
            rcases Nat.lt_or_ge 3618391497797 n with h12 | h12
            · -- n > 3618391497797
              exact RamareSaouter2003.prime_interval_nat_ladder_c02421 n (by omega) (by omega)
            · -- n <= 3618391497797
              exact RamareSaouter2003.prime_interval_nat_ladder_c02420 n (by omega) (by omega)
          · -- n <= 3609459039073
            exact RamareSaouter2003.prime_interval_nat_ladder_c02419 n (by omega) (by omega)
      · -- n <= 3600548631187
        rcases Nat.lt_or_ge 3573949169599 n with h8 | h8
        · -- n > 3573949169599
          rcases Nat.lt_or_ge 3582793750817 n with h10 | h10
          · -- n > 3582793750817
            rcases Nat.lt_or_ge 3591660219997 n with h12 | h12
            · -- n > 3591660219997
              exact RamareSaouter2003.prime_interval_nat_ladder_c02418 n (by omega) (by omega)
            · -- n <= 3591660219997
              exact RamareSaouter2003.prime_interval_nat_ladder_c02417 n (by omega) (by omega)
          · -- n <= 3582793750817
            exact RamareSaouter2003.prime_interval_nat_ladder_c02416 n (by omega) (by omega)
        · -- n <= 3573949169599
          rcases Nat.lt_or_ge 3556325455129 n with h10 | h10
          · -- n > 3556325455129
            rcases Nat.lt_or_ge 3565126422331 n with h12 | h12
            · -- n > 3565126422331
              exact RamareSaouter2003.prime_interval_nat_ladder_c02415 n (by omega) (by omega)
            · -- n <= 3565126422331
              exact RamareSaouter2003.prime_interval_nat_ladder_c02414 n (by omega) (by omega)
          · -- n <= 3556325455129
            exact RamareSaouter2003.prime_interval_nat_ladder_c02413 n (by omega) (by omega)
    · -- n <= 3547546214351
      rcases Nat.lt_or_ge 3495324027803 n with h6 | h6
      · -- n > 3495324027803
        rcases Nat.lt_or_ge 3521338314019 n with h8 | h8
        · -- n > 3521338314019
          rcases Nat.lt_or_ge 3530052697217 n with h10 | h10
          · -- n > 3530052697217
            rcases Nat.lt_or_ge 3538788646207 n with h12 | h12
            · -- n > 3538788646207
              exact RamareSaouter2003.prime_interval_nat_ladder_c02412 n (by omega) (by omega)
            · -- n <= 3538788646207
              exact RamareSaouter2003.prime_interval_nat_ladder_c02411 n (by omega) (by omega)
          · -- n <= 3530052697217
            exact RamareSaouter2003.prime_interval_nat_ladder_c02410 n (by omega) (by omega)
        · -- n <= 3521338314019
          rcases Nat.lt_or_ge 3503974032287 n with h10 | h10
          · -- n > 3503974032287
            rcases Nat.lt_or_ge 3512645443399 n with h12 | h12
            · -- n > 3512645443399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02409 n (by omega) (by omega)
            · -- n <= 3512645443399
              exact RamareSaouter2003.prime_interval_nat_ladder_c02408 n (by omega) (by omega)
          · -- n <= 3503974032287
            exact RamareSaouter2003.prime_interval_nat_ladder_c02407 n (by omega) (by omega)
      · -- n <= 3495324027803
        rcases Nat.lt_or_ge 3469501924817 n with h8 | h8
        · -- n > 3469501924817
          rcases Nat.lt_or_ge 3478088026681 n with h10 | h10
          · -- n > 3478088026681
            rcases Nat.lt_or_ge 3486695376851 n with h12 | h12
            · -- n > 3486695376851
              exact RamareSaouter2003.prime_interval_nat_ladder_c02406 n (by omega) (by omega)
            · -- n <= 3486695376851
              exact RamareSaouter2003.prime_interval_nat_ladder_c02405 n (by omega) (by omega)
          · -- n <= 3478088026681
            exact RamareSaouter2003.prime_interval_nat_ladder_c02404 n (by omega) (by omega)
        · -- n <= 3469501924817
          rcases Nat.lt_or_ge 3452393256451 n with h10 | h10
          · -- n > 3452393256451
            rcases Nat.lt_or_ge 3460937018873 n with h12 | h12
            · -- n > 3460937018873
              exact RamareSaouter2003.prime_interval_nat_ladder_c02403 n (by omega) (by omega)
            · -- n <= 3460937018873
              exact RamareSaouter2003.prime_interval_nat_ladder_c02402 n (by omega) (by omega)
          · -- n <= 3452393256451
            exact RamareSaouter2003.prime_interval_nat_ladder_c02401 n (by omega) (by omega)
