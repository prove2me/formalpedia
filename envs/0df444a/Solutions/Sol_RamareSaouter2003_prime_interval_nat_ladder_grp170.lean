-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T15:13:26.615326+00:00
-- url     : https://prove2.me/submissions/40433853-d866-4b11-ae53-7759ae592339

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08450
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08472

theorem solution (n : Nat)
    (hn : 43382410637006540717 < n) (hupper : n <= 48896242901857136909) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 46000691668654000969 n with h2 | h2
  · -- n > 46000691668654000969
    rcases Nat.lt_or_ge 47368507880699997883 n with h4 | h4
    · -- n > 47368507880699997883
      rcases Nat.lt_or_ge 48067592748582932117 n with h6 | h6
      · -- n > 48067592748582932117
        rcases Nat.lt_or_ge 48420994821335851241 n with h8 | h8
        · -- n > 48420994821335851241
          rcases Nat.lt_or_ge 48658038569315995361 n with h10 | h10
          · -- n > 48658038569315995361
            rcases Nat.lt_or_ge 48776995375816742291 n with h12 | h12
            · -- n > 48776995375816742291
              exact RamareSaouter2003.prime_interval_nat_ladder_c08472 n (by omega) (by omega)
            · -- n <= 48776995375816742291
              exact RamareSaouter2003.prime_interval_nat_ladder_c08471 n (by omega) (by omega)
          · -- n <= 48658038569315995361
            rcases Nat.lt_or_ge 48539372076389484539 n with h12 | h12
            · -- n > 48539372076389484539
              exact RamareSaouter2003.prime_interval_nat_ladder_c08470 n (by omega) (by omega)
            · -- n <= 48539372076389484539
              exact RamareSaouter2003.prime_interval_nat_ladder_c08469 n (by omega) (by omega)
        · -- n <= 48420994821335851241
          rcases Nat.lt_or_ge 48185106040783038209 n with h10 | h10
          · -- n > 48185106040783038209
            rcases Nat.lt_or_ge 48302906583351579431 n with h12 | h12
            · -- n > 48302906583351579431
              exact RamareSaouter2003.prime_interval_nat_ladder_c08468 n (by omega) (by omega)
            · -- n <= 48302906583351579431
              exact RamareSaouter2003.prime_interval_nat_ladder_c08467 n (by omega) (by omega)
          · -- n <= 48185106040783038209
            exact RamareSaouter2003.prime_interval_nat_ladder_c08466 n (by omega) (by omega)
      · -- n <= 48067592748582932117
        rcases Nat.lt_or_ge 47716769878561899097 n with h8 | h8
        · -- n > 47716769878561899097
          rcases Nat.lt_or_ge 47833425475489643849 n with h10 | h10
          · -- n > 47833425475489643849
            rcases Nat.lt_or_ge 47950366392843338657 n with h12 | h12
            · -- n > 47950366392843338657
              exact RamareSaouter2003.prime_interval_nat_ladder_c08465 n (by omega) (by omega)
            · -- n <= 47950366392843338657
              exact RamareSaouter2003.prime_interval_nat_ladder_c08464 n (by omega) (by omega)
          · -- n <= 47833425475489643849
            exact RamareSaouter2003.prime_interval_nat_ladder_c08463 n (by omega) (by omega)
        · -- n <= 47716769878561899097
          rcases Nat.lt_or_ge 47484311904152195273 n with h10 | h10
          · -- n > 47484311904152195273
            rcases Nat.lt_or_ge 47600398649800886581 n with h12 | h12
            · -- n > 47600398649800886581
              exact RamareSaouter2003.prime_interval_nat_ladder_c08462 n (by omega) (by omega)
            · -- n <= 47600398649800886581
              exact RamareSaouter2003.prime_interval_nat_ladder_c08461 n (by omega) (by omega)
          · -- n <= 47484311904152195273
            exact RamareSaouter2003.prime_interval_nat_ladder_c08460 n (by omega) (by omega)
    · -- n <= 47368507880699997883
      rcases Nat.lt_or_ge 46679589794267141759 n with h6 | h6
      · -- n > 46679589794267141759
        rcases Nat.lt_or_ge 47022787389260395963 n with h8 | h8
        · -- n > 47022787389260395963
          rcases Nat.lt_or_ge 47137746372145933799 n with h10 | h10
          · -- n > 47137746372145933799
            rcases Nat.lt_or_ge 47252986433510739743 n with h12 | h12
            · -- n > 47252986433510739743
              exact RamareSaouter2003.prime_interval_nat_ladder_c08459 n (by omega) (by omega)
            · -- n <= 47252986433510739743
              exact RamareSaouter2003.prime_interval_nat_ladder_c08458 n (by omega) (by omega)
          · -- n <= 47137746372145933799
            exact RamareSaouter2003.prime_interval_nat_ladder_c08457 n (by omega) (by omega)
        · -- n <= 47022787389260395963
          rcases Nat.lt_or_ge 46793709817941794203 n with h10 | h10
          · -- n > 46793709817941794203
            rcases Nat.lt_or_ge 46908108694666251829 n with h12 | h12
            · -- n > 46908108694666251829
              exact RamareSaouter2003.prime_interval_nat_ladder_c08456 n (by omega) (by omega)
            · -- n <= 46908108694666251829
              exact RamareSaouter2003.prime_interval_nat_ladder_c08455 n (by omega) (by omega)
          · -- n <= 46793709817941794203
            exact RamareSaouter2003.prime_interval_nat_ladder_c08454 n (by omega) (by omega)
      · -- n <= 46679589794267141759
        rcases Nat.lt_or_ge 46338897547230286489 n with h8 | h8
        · -- n > 46338897547230286489
          rcases Nat.lt_or_ge 46452184447862940583 n with h10 | h10
          · -- n > 46452184447862940583
            rcases Nat.lt_or_ge 46565748033783727927 n with h12 | h12
            · -- n > 46565748033783727927
              exact RamareSaouter2003.prime_interval_nat_ladder_c08453 n (by omega) (by omega)
            · -- n <= 46565748033783727927
              exact RamareSaouter2003.prime_interval_nat_ladder_c08452 n (by omega) (by omega)
          · -- n <= 46452184447862940583
            exact RamareSaouter2003.prime_interval_nat_ladder_c08451 n (by omega) (by omega)
        · -- n <= 46338897547230286489
          rcases Nat.lt_or_ge 46113151969243264603 n with h10 | h10
          · -- n > 46113151969243264603
            rcases Nat.lt_or_ge 46225887220774254899 n with h12 | h12
            · -- n > 46225887220774254899
              exact RamareSaouter2003.prime_interval_nat_ladder_c08450 n (by omega) (by omega)
            · -- n <= 46225887220774254899
              exact RamareSaouter2003.prime_interval_nat_ladder_c08449 n (by omega) (by omega)
          · -- n <= 46113151969243264603
            exact RamareSaouter2003.prime_interval_nat_ladder_c08448 n (by omega) (by omega)
  · -- n <= 46000691668654000969
    rcases Nat.lt_or_ge 44672373621690855701 n with h4 | h4
    · -- n > 44672373621690855701
      rcases Nat.lt_or_ge 45331667003494429163 n with h6 | h6
      · -- n > 45331667003494429163
        rcases Nat.lt_or_ge 45664954243279923841 n with h8 | h8
        · -- n > 45664954243279923841
          rcases Nat.lt_or_ge 45776593524530198221 n with h10 | h10
          · -- n > 45776593524530198221
            rcases Nat.lt_or_ge 45888505589961178399 n with h12 | h12
            · -- n > 45888505589961178399
              exact RamareSaouter2003.prime_interval_nat_ladder_c08447 n (by omega) (by omega)
            · -- n <= 45888505589961178399
              exact RamareSaouter2003.prime_interval_nat_ladder_c08446 n (by omega) (by omega)
          · -- n <= 45776593524530198221
            exact RamareSaouter2003.prime_interval_nat_ladder_c08445 n (by omega) (by omega)
        · -- n <= 45664954243279923841
          rcases Nat.lt_or_ge 45442491655502573683 n with h10 | h10
          · -- n > 45442491655502573683
            rcases Nat.lt_or_ge 45553587312904074931 n with h12 | h12
            · -- n > 45553587312904074931
              exact RamareSaouter2003.prime_interval_nat_ladder_c08444 n (by omega) (by omega)
            · -- n <= 45553587312904074931
              exact RamareSaouter2003.prime_interval_nat_ladder_c08443 n (by omega) (by omega)
          · -- n <= 45442491655502573683
            exact RamareSaouter2003.prime_interval_nat_ladder_c08442 n (by omega) (by omega)
      · -- n <= 45331667003494429163
        rcases Nat.lt_or_ge 45000812880845170967 n with h8 | h8
        · -- n > 45000812880845170967
          rcases Nat.lt_or_ge 45110828104023883609 n with h10 | h10
          · -- n > 45110828104023883609
            rcases Nat.lt_or_ge 45221112902944692139 n with h12 | h12
            · -- n > 45221112902944692139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08441 n (by omega) (by omega)
            · -- n <= 45221112902944692139
              exact RamareSaouter2003.prime_interval_nat_ladder_c08440 n (by omega) (by omega)
          · -- n <= 45110828104023883609
            exact RamareSaouter2003.prime_interval_nat_ladder_c08439 n (by omega) (by omega)
        · -- n <= 45000812880845170967
          rcases Nat.lt_or_ge 44781586557519474059 n with h10 | h10
          · -- n > 44781586557519474059
            rcases Nat.lt_or_ge 44891065705357660417 n with h12 | h12
            · -- n > 44891065705357660417
              exact RamareSaouter2003.prime_interval_nat_ladder_c08438 n (by omega) (by omega)
            · -- n <= 44891065705357660417
              exact RamareSaouter2003.prime_interval_nat_ladder_c08437 n (by omega) (by omega)
          · -- n <= 44781586557519474059
            exact RamareSaouter2003.prime_interval_nat_ladder_c08436 n (by omega) (by omega)
    · -- n <= 44672373621690855701
      rcases Nat.lt_or_ge 44022667435523166127 n with h6 | h6
      · -- n > 44022667435523166127
        rcases Nat.lt_or_ge 44346330828614230453 n with h8 | h8
        · -- n > 44346330828614230453
          rcases Nat.lt_or_ge 44454746643298088921 n with h10 | h10
          · -- n > 44454746643298088921
            rcases Nat.lt_or_ge 44563427333428606997 n with h12 | h12
            · -- n > 44563427333428606997
              exact RamareSaouter2003.prime_interval_nat_ladder_c08435 n (by omega) (by omega)
            · -- n <= 44563427333428606997
              exact RamareSaouter2003.prime_interval_nat_ladder_c08434 n (by omega) (by omega)
          · -- n <= 44454746643298088921
            exact RamareSaouter2003.prime_interval_nat_ladder_c08433 n (by omega) (by omega)
        · -- n <= 44346330828614230453
          rcases Nat.lt_or_ge 44130291959931299711 n with h10 | h10
          · -- n > 44130291959931299711
            rcases Nat.lt_or_ge 44238179440005300943 n with h12 | h12
            · -- n > 44238179440005300943
              exact RamareSaouter2003.prime_interval_nat_ladder_c08432 n (by omega) (by omega)
            · -- n <= 44238179440005300943
              exact RamareSaouter2003.prime_interval_nat_ladder_c08431 n (by omega) (by omega)
          · -- n <= 44130291959931299711
            exact RamareSaouter2003.prime_interval_nat_ladder_c08430 n (by omega) (by omega)
      · -- n <= 44022667435523166127
        rcases Nat.lt_or_ge 43701366626237790037 n with h8 | h8
        · -- n > 43701366626237790037
          rcases Nat.lt_or_ge 43808205612658382537 n with h10 | h10
          · -- n > 43808205612658382537
            rcases Nat.lt_or_ge 43915305452150207267 n with h12 | h12
            · -- n > 43915305452150207267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08429 n (by omega) (by omega)
            · -- n <= 43915305452150207267
              exact RamareSaouter2003.prime_interval_nat_ladder_c08428 n (by omega) (by omega)
          · -- n <= 43808205612658382537
            exact RamareSaouter2003.prime_interval_nat_ladder_c08427 n (by omega) (by omega)
        · -- n <= 43701366626237790037
          rcases Nat.lt_or_ge 43488469588277521253 n with h10 | h10
          · -- n > 43488469588277521253
            rcases Nat.lt_or_ge 43594788111167080877 n with h12 | h12
            · -- n > 43594788111167080877
              exact RamareSaouter2003.prime_interval_nat_ladder_c08426 n (by omega) (by omega)
            · -- n <= 43594788111167080877
              exact RamareSaouter2003.prime_interval_nat_ladder_c08425 n (by omega) (by omega)
          · -- n <= 43488469588277521253
            exact RamareSaouter2003.prime_interval_nat_ladder_c08424 n (by omega) (by omega)
