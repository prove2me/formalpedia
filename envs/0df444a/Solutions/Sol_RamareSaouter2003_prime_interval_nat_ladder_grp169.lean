-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T14:51:18.460254+00:00
-- url     : https://prove2.me/submissions/a98e586d-ab1c-4f7e-807f-f87e6090aa62

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08400
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08423

theorem solution (n : Nat)
    (hn : 38490349635789503129 < n) (hupper : n <= 43382410637006540717) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 40813379352805391599 n with h2 | h2
  · -- n > 40813379352805391599
    rcases Nat.lt_or_ge 42026951936111986213 n with h4 | h4
    · -- n > 42026951936111986213
      rcases Nat.lt_or_ge 42647204542021074461 n with h6 | h6
      · -- n > 42647204542021074461
        rcases Nat.lt_or_ge 42960755327438478311 n with h8 | h8
        · -- n > 42960755327438478311
          rcases Nat.lt_or_ge 43171068451578091099 n with h10 | h10
          · -- n > 43171068451578091099
            rcases Nat.lt_or_ge 43276610133792111049 n with h12 | h12
            · -- n > 43276610133792111049
              exact RamareSaouter2003.prime_interval_nat_ladder_c08423 n (by omega) (by omega)
            · -- n <= 43276610133792111049
              exact RamareSaouter2003.prime_interval_nat_ladder_c08422 n (by omega) (by omega)
          · -- n <= 43171068451578091099
            rcases Nat.lt_or_ge 43065783562786271251 n with h12 | h12
            · -- n > 43065783562786271251
              exact RamareSaouter2003.prime_interval_nat_ladder_c08421 n (by omega) (by omega)
            · -- n <= 43065783562786271251
              exact RamareSaouter2003.prime_interval_nat_ladder_c08420 n (by omega) (by omega)
        · -- n <= 42960755327438478311
          rcases Nat.lt_or_ge 42751466442396204047 n with h10 | h10
          · -- n > 42751466442396204047
            rcases Nat.lt_or_ge 42855983118428713867 n with h12 | h12
            · -- n > 42855983118428713867
              exact RamareSaouter2003.prime_interval_nat_ladder_c08419 n (by omega) (by omega)
            · -- n <= 42855983118428713867
              exact RamareSaouter2003.prime_interval_nat_ladder_c08418 n (by omega) (by omega)
          · -- n <= 42751466442396204047
            exact RamareSaouter2003.prime_interval_nat_ladder_c08417 n (by omega) (by omega)
      · -- n <= 42647204542021074461
        rcases Nat.lt_or_ge 42335942343051234641 n with h8 | h8
        · -- n > 42335942343051234641
          rcases Nat.lt_or_ge 42439443238342581203 n with h10 | h10
          · -- n > 42439443238342581203
            rcases Nat.lt_or_ge 42543196993902939583 n with h12 | h12
            · -- n > 42543196993902939583
              exact RamareSaouter2003.prime_interval_nat_ladder_c08416 n (by omega) (by omega)
            · -- n <= 42543196993902939583
              exact RamareSaouter2003.prime_interval_nat_ladder_c08415 n (by omega) (by omega)
          · -- n <= 42439443238342581203
            exact RamareSaouter2003.prime_interval_nat_ladder_c08414 n (by omega) (by omega)
        · -- n <= 42335942343051234641
          rcases Nat.lt_or_ge 42129697217464066453 n with h10 | h10
          · -- n > 42129697217464066453
            rcases Nat.lt_or_ge 42232693844896651387 n with h12 | h12
            · -- n > 42232693844896651387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08413 n (by omega) (by omega)
            · -- n <= 42232693844896651387
              exact RamareSaouter2003.prime_interval_nat_ladder_c08412 n (by omega) (by omega)
          · -- n <= 42129697217464066453
            exact RamareSaouter2003.prime_interval_nat_ladder_c08411 n (by omega) (by omega)
    · -- n <= 42026951936111986213
      rcases Nat.lt_or_ge 41415721192388677861 n with h6 | h6
      · -- n > 41415721192388677861
        rcases Nat.lt_or_ge 41720217376422200003 n with h8 | h8
        · -- n > 41720217376422200003
          rcases Nat.lt_or_ge 41822212583049068537 n with h10 | h10
          · -- n > 41822212583049068537
            rcases Nat.lt_or_ge 41924457409262324711 n with h12 | h12
            · -- n > 41924457409262324711
              exact RamareSaouter2003.prime_interval_nat_ladder_c08410 n (by omega) (by omega)
            · -- n <= 41924457409262324711
              exact RamareSaouter2003.prime_interval_nat_ladder_c08409 n (by omega) (by omega)
          · -- n <= 41822212583049068537
            exact RamareSaouter2003.prime_interval_nat_ladder_c08408 n (by omega) (by omega)
        · -- n <= 41720217376422200003
          rcases Nat.lt_or_ge 41516972134426331593 n with h10 | h10
          · -- n > 41516972134426331593
            rcases Nat.lt_or_ge 41618470673181004193 n with h12 | h12
            · -- n > 41618470673181004193
              exact RamareSaouter2003.prime_interval_nat_ladder_c08407 n (by omega) (by omega)
            · -- n <= 41618470673181004193
              exact RamareSaouter2003.prime_interval_nat_ladder_c08406 n (by omega) (by omega)
          · -- n <= 41516972134426331593
            exact RamareSaouter2003.prime_interval_nat_ladder_c08405 n (by omega) (by omega)
      · -- n <= 41415721192388677861
        rcases Nat.lt_or_ge 41113447070943391153 n with h8 | h8
        · -- n > 41113447070943391153
          rcases Nat.lt_or_ge 41213958982678746581 n with h10 | h10
          · -- n > 41213958982678746581
            rcases Nat.lt_or_ge 41314716928206819541 n with h12 | h12
            · -- n > 41314716928206819541
              exact RamareSaouter2003.prime_interval_nat_ladder_c08404 n (by omega) (by omega)
            · -- n <= 41314716928206819541
              exact RamareSaouter2003.prime_interval_nat_ladder_c08403 n (by omega) (by omega)
          · -- n <= 41213958982678746581
            exact RamareSaouter2003.prime_interval_nat_ladder_c08402 n (by omega) (by omega)
        · -- n <= 41113447070943391153
          rcases Nat.lt_or_ge 40913157843966949967 n with h10 | h10
          · -- n > 40913157843966949967
            rcases Nat.lt_or_ge 41013180139932488819 n with h12 | h12
            · -- n > 41013180139932488819
              exact RamareSaouter2003.prime_interval_nat_ladder_c08401 n (by omega) (by omega)
            · -- n <= 41013180139932488819
              exact RamareSaouter2003.prime_interval_nat_ladder_c08400 n (by omega) (by omega)
          · -- n <= 40913157843966949967
            exact RamareSaouter2003.prime_interval_nat_ladder_c08399 n (by omega) (by omega)
  · -- n <= 40813379352805391599
    rcases Nat.lt_or_ge 39634848589113027163 n with h4 | h4
    · -- n > 39634848589113027163
      rcases Nat.lt_or_ge 40219797594261651997 n with h6 | h6
      · -- n > 40219797594261651997
        rcases Nat.lt_or_ge 40515501749235661513 n with h8 | h8
        · -- n > 40515501749235661513
          rcases Nat.lt_or_ge 40614552152106630083 n with h10 | h10
          · -- n > 40614552152106630083
            rcases Nat.lt_or_ge 40713844474755259411 n with h12 | h12
            · -- n > 40713844474755259411
              exact RamareSaouter2003.prime_interval_nat_ladder_c08398 n (by omega) (by omega)
            · -- n <= 40713844474755259411
              exact RamareSaouter2003.prime_interval_nat_ladder_c08397 n (by omega) (by omega)
          · -- n <= 40614552152106630083
            exact RamareSaouter2003.prime_interval_nat_ladder_c08396 n (by omega) (by omega)
        · -- n <= 40515501749235661513
          rcases Nat.lt_or_ge 40318125064579816891 n with h10 | h10
          · -- n > 40318125064579816891
            rcases Nat.lt_or_ge 40416692901200432233 n with h12 | h12
            · -- n > 40416692901200432233
              exact RamareSaouter2003.prime_interval_nat_ladder_c08395 n (by omega) (by omega)
            · -- n <= 40416692901200432233
              exact RamareSaouter2003.prime_interval_nat_ladder_c08394 n (by omega) (by omega)
          · -- n <= 40318125064579816891
            exact RamareSaouter2003.prime_interval_nat_ladder_c08393 n (by omega) (by omega)
      · -- n <= 40219797594261651997
        rcases Nat.lt_or_ge 39926251699537070249 n with h8 | h8
        · -- n > 39926251699537070249
          rcases Nat.lt_or_ge 40023861527571851603 n with h10 | h10
          · -- n > 40023861527571851603
            rcases Nat.lt_or_ge 40121709975478928231 n with h12 | h12
            · -- n > 40121709975478928231
              exact RamareSaouter2003.prime_interval_nat_ladder_c08392 n (by omega) (by omega)
            · -- n <= 40121709975478928231
              exact RamareSaouter2003.prime_interval_nat_ladder_c08391 n (by omega) (by omega)
          · -- n <= 40023861527571851603
            exact RamareSaouter2003.prime_interval_nat_ladder_c08390 n (by omega) (by omega)
        · -- n <= 39926251699537070249
          rcases Nat.lt_or_ge 39731745981059572579 n with h10 | h10
          · -- n > 39731745981059572579
            rcases Nat.lt_or_ge 39828880180577217061 n with h12 | h12
            · -- n > 39828880180577217061
              exact RamareSaouter2003.prime_interval_nat_ladder_c08389 n (by omega) (by omega)
            · -- n <= 39828880180577217061
              exact RamareSaouter2003.prime_interval_nat_ladder_c08388 n (by omega) (by omega)
          · -- n <= 39731745981059572579
            exact RamareSaouter2003.prime_interval_nat_ladder_c08387 n (by omega) (by omega)
    · -- n <= 39634848589113027163
      rcases Nat.lt_or_ge 39058407332951149421 n with h6 | h6
      · -- n > 39058407332951149421
        rcases Nat.lt_or_ge 39345572572448113399 n with h8 | h8
        · -- n > 39345572572448113399
          rcases Nat.lt_or_ge 39441762536840198861 n with h10 | h10
          · -- n > 39441762536840198861
            rcases Nat.lt_or_ge 39538187874182117909 n with h12 | h12
            · -- n > 39538187874182117909
              exact RamareSaouter2003.prime_interval_nat_ladder_c08386 n (by omega) (by omega)
            · -- n <= 39538187874182117909
              exact RamareSaouter2003.prime_interval_nat_ladder_c08385 n (by omega) (by omega)
          · -- n <= 39441762536840198861
            exact RamareSaouter2003.prime_interval_nat_ladder_c08384 n (by omega) (by omega)
        · -- n <= 39345572572448113399
          rcases Nat.lt_or_ge 39153895486214248403 n with h10 | h10
          · -- n > 39153895486214248403
            rcases Nat.lt_or_ge 39249617086261524799 n with h12 | h12
            · -- n > 39249617086261524799
              exact RamareSaouter2003.prime_interval_nat_ladder_c08383 n (by omega) (by omega)
            · -- n <= 39249617086261524799
              exact RamareSaouter2003.prime_interval_nat_ladder_c08382 n (by omega) (by omega)
          · -- n <= 39153895486214248403
            exact RamareSaouter2003.prime_interval_nat_ladder_c08381 n (by omega) (by omega)
      · -- n <= 39058407332951149421
        rcases Nat.lt_or_ge 38773337860615662851 n with h8 | h8
        · -- n > 38773337860615662851
          rcases Nat.lt_or_ge 38868129107686286999 n with h10 | h10
          · -- n > 38868129107686286999
            rcases Nat.lt_or_ge 38963152048754478653 n with h12 | h12
            · -- n > 38963152048754478653
              exact RamareSaouter2003.prime_interval_nat_ladder_c08380 n (by omega) (by omega)
            · -- n <= 38963152048754478653
              exact RamareSaouter2003.prime_interval_nat_ladder_c08379 n (by omega) (by omega)
          · -- n <= 38868129107686286999
            exact RamareSaouter2003.prime_interval_nat_ladder_c08378 n (by omega) (by omega)
        · -- n <= 38773337860615662851
          rcases Nat.lt_or_ge 38584448825986635511 n with h10 | h10
          · -- n > 38584448825986635511
            rcases Nat.lt_or_ge 38678778032692599017 n with h12 | h12
            · -- n > 38678778032692599017
              exact RamareSaouter2003.prime_interval_nat_ladder_c08377 n (by omega) (by omega)
            · -- n <= 38678778032692599017
              exact RamareSaouter2003.prime_interval_nat_ladder_c08376 n (by omega) (by omega)
          · -- n <= 38584448825986635511
            exact RamareSaouter2003.prime_interval_nat_ladder_c08375 n (by omega) (by omega)
