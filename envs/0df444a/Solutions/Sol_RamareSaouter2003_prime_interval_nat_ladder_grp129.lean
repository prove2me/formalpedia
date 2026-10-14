-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T23:05:29.163183+00:00
-- url     : https://prove2.me/submissions/484e2682-cfe2-42f9-ae0e-cb50d8c6b1b6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06450

theorem solution (n : Nat)
    (hn : 162905024672217103 < n) (hupper : n <= 187640393798056393) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 174835680087082969 n with h2 | h2
  · -- n > 174835680087082969
    rcases Nat.lt_or_ge 180869019075482587 n with h4 | h4
    · -- n > 180869019075482587
      rcases Nat.lt_or_ge 183963345397321297 n with h6 | h6
      · -- n > 183963345397321297
        rcases Nat.lt_or_ge 185530337266364219 n with h8 | h8
        · -- n > 185530337266364219
          rcases Nat.lt_or_ge 186582395147301397 n with h10 | h10
          · -- n > 186582395147301397
            rcases Nat.lt_or_ge 187110648947561513 n with h12 | h12
            · -- n > 187110648947561513
              exact RamareSaouter2003.prime_interval_nat_ladder_c06450 n (by omega) (by omega)
            · -- n <= 187110648947561513
              exact RamareSaouter2003.prime_interval_nat_ladder_c06449 n (by omega) (by omega)
          · -- n <= 186582395147301397
            rcases Nat.lt_or_ge 186055619564288681 n with h12 | h12
            · -- n > 186055619564288681
              exact RamareSaouter2003.prime_interval_nat_ladder_c06448 n (by omega) (by omega)
            · -- n <= 186055619564288681
              exact RamareSaouter2003.prime_interval_nat_ladder_c06447 n (by omega) (by omega)
        · -- n <= 185530337266364219
          rcases Nat.lt_or_ge 184484200301559911 n with h10 | h10
          · -- n > 184484200301559911
            rcases Nat.lt_or_ge 185006527869827119 n with h12 | h12
            · -- n > 185006527869827119
              exact RamareSaouter2003.prime_interval_nat_ladder_c06446 n (by omega) (by omega)
            · -- n <= 185006527869827119
              exact RamareSaouter2003.prime_interval_nat_ladder_c06445 n (by omega) (by omega)
          · -- n <= 184484200301559911
            exact RamareSaouter2003.prime_interval_nat_ladder_c06444 n (by omega) (by omega)
      · -- n <= 183963345397321297
        rcases Nat.lt_or_ge 182409644589022789 n with h8 | h8
        · -- n > 182409644589022789
          rcases Nat.lt_or_ge 182926065115076957 n with h10 | h10
          · -- n > 182926065115076957
            rcases Nat.lt_or_ge 183443983185960859 n with h12 | h12
            · -- n > 183443983185960859
              exact RamareSaouter2003.prime_interval_nat_ladder_c06443 n (by omega) (by omega)
            · -- n <= 183443983185960859
              exact RamareSaouter2003.prime_interval_nat_ladder_c06442 n (by omega) (by omega)
          · -- n <= 182926065115076957
            exact RamareSaouter2003.prime_interval_nat_ladder_c06441 n (by omega) (by omega)
        · -- n <= 182409644589022789
          rcases Nat.lt_or_ge 181381106664658027 n with h10 | h10
          · -- n > 181381106664658027
            rcases Nat.lt_or_ge 181894645782480061 n with h12 | h12
            · -- n > 181894645782480061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06440 n (by omega) (by omega)
            · -- n <= 181894645782480061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06439 n (by omega) (by omega)
          · -- n <= 181381106664658027
            exact RamareSaouter2003.prime_interval_nat_ladder_c06438 n (by omega) (by omega)
    · -- n <= 180869019075482587
      rcases Nat.lt_or_ge 177826775766480011 n with h6 | h6
      · -- n > 177826775766480011
        rcases Nat.lt_or_ge 179341480201926517 n with h8 | h8
        · -- n > 179341480201926517
          rcases Nat.lt_or_ge 179849208940090999 n with h10 | h10
          · -- n > 179849208940090999
            rcases Nat.lt_or_ge 180358383285641089 n with h12 | h12
            · -- n > 180358383285641089
              exact RamareSaouter2003.prime_interval_nat_ladder_c06437 n (by omega) (by omega)
            · -- n <= 180358383285641089
              exact RamareSaouter2003.prime_interval_nat_ladder_c06436 n (by omega) (by omega)
          · -- n <= 179849208940090999
            exact RamareSaouter2003.prime_interval_nat_ladder_c06435 n (by omega) (by omega)
        · -- n <= 179341480201926517
          rcases Nat.lt_or_ge 178330250954484053 n with h10 | h10
          · -- n > 178330250954484053
            rcases Nat.lt_or_ge 178835143252642823 n with h12 | h12
            · -- n > 178835143252642823
              exact RamareSaouter2003.prime_interval_nat_ladder_c06434 n (by omega) (by omega)
            · -- n <= 178835143252642823
              exact RamareSaouter2003.prime_interval_nat_ladder_c06433 n (by omega) (by omega)
          · -- n <= 178330250954484053
            exact RamareSaouter2003.prime_interval_nat_ladder_c06432 n (by omega) (by omega)
      · -- n <= 177826775766480011
        rcases Nat.lt_or_ge 176324875929651751 n with h8 | h8
        · -- n > 176324875929651751
          rcases Nat.lt_or_ge 176824100088532129 n with h10 | h10
          · -- n > 176824100088532129
            rcases Nat.lt_or_ge 177324732380851169 n with h12 | h12
            · -- n > 177324732380851169
              exact RamareSaouter2003.prime_interval_nat_ladder_c06431 n (by omega) (by omega)
            · -- n <= 177324732380851169
              exact RamareSaouter2003.prime_interval_nat_ladder_c06430 n (by omega) (by omega)
          · -- n <= 176824100088532129
            exact RamareSaouter2003.prime_interval_nat_ladder_c06429 n (by omega) (by omega)
        · -- n <= 176324875929651751
          rcases Nat.lt_or_ge 175330666807345733 n with h10 | h10
          · -- n > 175330666807345733
            rcases Nat.lt_or_ge 175827056022172993 n with h12 | h12
            · -- n > 175827056022172993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06428 n (by omega) (by omega)
            · -- n <= 175827056022172993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06427 n (by omega) (by omega)
          · -- n <= 175330666807345733
            exact RamareSaouter2003.prime_interval_nat_ladder_c06426 n (by omega) (by omega)
  · -- n <= 174835680087082969
    rcases Nat.lt_or_ge 168526448901718333 n with h4 | h4
    · -- n > 168526448901718333
      rcases Nat.lt_or_ge 171409631436145471 n with h6 | h6
      · -- n > 171409631436145471
        rcases Nat.lt_or_ge 172869611132142713 n with h8 | h8
        · -- n > 172869611132142713
          rcases Nat.lt_or_ge 173849859576097891 n with h10 | h10
          · -- n > 173849859576097891
            rcases Nat.lt_or_ge 174342065275659607 n with h12 | h12
            · -- n > 174342065275659607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06425 n (by omega) (by omega)
            · -- n <= 174342065275659607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06424 n (by omega) (by omega)
          · -- n <= 173849859576097891
            rcases Nat.lt_or_ge 173359037522266009 n with h12 | h12
            · -- n > 173359037522266009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06423 n (by omega) (by omega)
            · -- n <= 173359037522266009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06422 n (by omega) (by omega)
        · -- n <= 172869611132142713
          rcases Nat.lt_or_ge 171894910196906657 n with h10 | h10
          · -- n > 171894910196906657
            rcases Nat.lt_or_ge 172381548316383001 n with h12 | h12
            · -- n > 172381548316383001
              exact RamareSaouter2003.prime_interval_nat_ladder_c06421 n (by omega) (by omega)
            · -- n <= 172381548316383001
              exact RamareSaouter2003.prime_interval_nat_ladder_c06420 n (by omega) (by omega)
          · -- n <= 171894910196906657
            exact RamareSaouter2003.prime_interval_nat_ladder_c06419 n (by omega) (by omega)
      · -- n <= 171409631436145471
        rcases Nat.lt_or_ge 169961920661139917 n with h8 | h8
        · -- n > 169961920661139917
          rcases Nat.lt_or_ge 170443126724287799 n with h10 | h10
          · -- n > 170443126724287799
            rcases Nat.lt_or_ge 170925691886945087 n with h12 | h12
            · -- n > 170925691886945087
              exact RamareSaouter2003.prime_interval_nat_ladder_c06418 n (by omega) (by omega)
            · -- n <= 170925691886945087
              exact RamareSaouter2003.prime_interval_nat_ladder_c06417 n (by omega) (by omega)
          · -- n <= 170443126724287799
            exact RamareSaouter2003.prime_interval_nat_ladder_c06416 n (by omega) (by omega)
        · -- n <= 169961920661139917
          rcases Nat.lt_or_ge 169003571059707089 n with h10 | h10
          · -- n > 169003571059707089
            rcases Nat.lt_or_ge 169482067543548611 n with h12 | h12
            · -- n > 169482067543548611
              exact RamareSaouter2003.prime_interval_nat_ladder_c06415 n (by omega) (by omega)
            · -- n <= 169482067543548611
              exact RamareSaouter2003.prime_interval_nat_ladder_c06414 n (by omega) (by omega)
          · -- n <= 169003571059707089
            exact RamareSaouter2003.prime_interval_nat_ladder_c06413 n (by omega) (by omega)
    · -- n <= 168526448901718333
      rcases Nat.lt_or_ge 165691929601239523 n with h6 | h6
      · -- n > 165691929601239523
        rcases Nat.lt_or_ge 167103136746087803 n with h8 | h8
        · -- n > 167103136746087803
          rcases Nat.lt_or_ge 167576232098240813 n with h10 | h10
          · -- n > 167576232098240813
            rcases Nat.lt_or_ge 168050666097729643 n with h12 | h12
            · -- n > 168050666097729643
              exact RamareSaouter2003.prime_interval_nat_ladder_c06412 n (by omega) (by omega)
            · -- n <= 168050666097729643
              exact RamareSaouter2003.prime_interval_nat_ladder_c06411 n (by omega) (by omega)
          · -- n <= 167576232098240813
            exact RamareSaouter2003.prime_interval_nat_ladder_c06410 n (by omega) (by omega)
        · -- n <= 167103136746087803
          rcases Nat.lt_or_ge 166160980593375589 n with h10 | h10
          · -- n > 166160980593375589
            rcases Nat.lt_or_ge 166631387732040983 n with h12 | h12
            · -- n > 166631387732040983
              exact RamareSaouter2003.prime_interval_nat_ladder_c06409 n (by omega) (by omega)
            · -- n <= 166631387732040983
              exact RamareSaouter2003.prime_interval_nat_ladder_c06408 n (by omega) (by omega)
          · -- n <= 166160980593375589
            exact RamareSaouter2003.prime_interval_nat_ladder_c06407 n (by omega) (by omega)
      · -- n <= 165691929601239523
        rcases Nat.lt_or_ge 164292555518854963 n with h8 | h8
        · -- n > 164292555518854963
          rcases Nat.lt_or_ge 164757716077162889 n with h10 | h10
          · -- n > 164757716077162889
            rcases Nat.lt_or_ge 165224135789774839 n with h12 | h12
            · -- n > 165224135789774839
              exact RamareSaouter2003.prime_interval_nat_ladder_c06406 n (by omega) (by omega)
            · -- n <= 165224135789774839
              exact RamareSaouter2003.prime_interval_nat_ladder_c06405 n (by omega) (by omega)
          · -- n <= 164757716077162889
            exact RamareSaouter2003.prime_interval_nat_ladder_c06404 n (by omega) (by omega)
        · -- n <= 164292555518854963
          rcases Nat.lt_or_ge 163366221525658421 n with h10 | h10
          · -- n > 163366221525658421
            rcases Nat.lt_or_ge 163828717111792561 n with h12 | h12
            · -- n > 163828717111792561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06403 n (by omega) (by omega)
            · -- n <= 163828717111792561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06402 n (by omega) (by omega)
          · -- n <= 163366221525658421
            exact RamareSaouter2003.prime_interval_nat_ladder_c06401 n (by omega) (by omega)
