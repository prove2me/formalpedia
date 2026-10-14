-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T08:35:26.506268+00:00
-- url     : https://prove2.me/submissions/4b178380-1ab4-4005-9e56-7fe55e63447c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07600
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07639

theorem solution (n : Nat)
    (hn : 4710784340673854327 < n) (hupper : n <= 5410770793340726459) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 5041528889912863657 n with h2 | h2
  · -- n > 5041528889912863657
    rcases Nat.lt_or_ge 5215510021566622079 n with h4 | h4
    · -- n > 5215510021566622079
      rcases Nat.lt_or_ge 5304739415369836259 n with h6 | h6
      · -- n > 5304739415369836259
        rcases Nat.lt_or_ge 5349924297334533179 n with h8 | h8
        · -- n > 5349924297334533179
          rcases Nat.lt_or_ge 5380261626360115307 n with h10 | h10
          · -- n > 5380261626360115307
            rcases Nat.lt_or_ge 5395494770555674079 n with h12 | h12
            · -- n > 5395494770555674079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07639 n (by omega) (by omega)
            · -- n <= 5395494770555674079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07638 n (by omega) (by omega)
          · -- n <= 5380261626360115307
            rcases Nat.lt_or_ge 5365071571255117121 n with h12 | h12
            · -- n > 5365071571255117121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07637 n (by omega) (by omega)
            · -- n <= 5365071571255117121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07636 n (by omega) (by omega)
        · -- n <= 5349924297334533179
          rcases Nat.lt_or_ge 5319758503852413839 n with h10 | h10
          · -- n > 5319758503852413839
            rcases Nat.lt_or_ge 5334819948659027459 n with h12 | h12
            · -- n > 5334819948659027459
              exact RamareSaouter2003.prime_interval_nat_ladder_c07635 n (by omega) (by omega)
            · -- n <= 5334819948659027459
              exact RamareSaouter2003.prime_interval_nat_ladder_c07634 n (by omega) (by omega)
          · -- n <= 5319758503852413839
            exact RamareSaouter2003.prime_interval_nat_ladder_c07633 n (by omega) (by omega)
      · -- n <= 5304739415369836259
        rcases Nat.lt_or_ge 5259935525525974703 n with h8 | h8
        · -- n > 5259935525525974703
          rcases Nat.lt_or_ge 5274827953392114437 n with h10 | h10
          · -- n > 5274827953392114437
            rcases Nat.lt_or_ge 5289762556581230083 n with h12 | h12
            · -- n > 5289762556581230083
              exact RamareSaouter2003.prime_interval_nat_ladder_c07632 n (by omega) (by omega)
            · -- n <= 5289762556581230083
              exact RamareSaouter2003.prime_interval_nat_ladder_c07631 n (by omega) (by omega)
          · -- n <= 5274827953392114437
            exact RamareSaouter2003.prime_interval_nat_ladder_c07630 n (by omega) (by omega)
        · -- n <= 5259935525525974703
          rcases Nat.lt_or_ge 5230276710055359223 n with h10 | h10
          · -- n > 5230276710055359223
            rcases Nat.lt_or_ge 5245085101117156891 n with h12 | h12
            · -- n > 5245085101117156891
              exact RamareSaouter2003.prime_interval_nat_ladder_c07629 n (by omega) (by omega)
            · -- n <= 5245085101117156891
              exact RamareSaouter2003.prime_interval_nat_ladder_c07628 n (by omega) (by omega)
          · -- n <= 5230276710055359223
            exact RamareSaouter2003.prime_interval_nat_ladder_c07627 n (by omega) (by omega)
    · -- n <= 5215510021566622079
      rcases Nat.lt_or_ge 5127781603859130497 n with h6 | h6
      · -- n > 5127781603859130497
        rcases Nat.lt_or_ge 5171459787823361887 n with h8 | h8
        · -- n > 5171459787823361887
          rcases Nat.lt_or_ge 5186101753479872783 n with h10 | h10
          · -- n > 5186101753479872783
            rcases Nat.lt_or_ge 5200785070034863717 n with h12 | h12
            · -- n > 5200785070034863717
              exact RamareSaouter2003.prime_interval_nat_ladder_c07626 n (by omega) (by omega)
            · -- n <= 5200785070034863717
              exact RamareSaouter2003.prime_interval_nat_ladder_c07625 n (by omega) (by omega)
          · -- n <= 5186101753479872783
            exact RamareSaouter2003.prime_interval_nat_ladder_c07624 n (by omega) (by omega)
        · -- n <= 5171459787823361887
          rcases Nat.lt_or_ge 5142299791518319411 n with h10 | h10
          · -- n > 5142299791518319411
            rcases Nat.lt_or_ge 5156859153843811283 n with h12 | h12
            · -- n > 5156859153843811283
              exact RamareSaouter2003.prime_interval_nat_ladder_c07623 n (by omega) (by omega)
            · -- n <= 5156859153843811283
              exact RamareSaouter2003.prime_interval_nat_ladder_c07622 n (by omega) (by omega)
          · -- n <= 5142299791518319411
            exact RamareSaouter2003.prime_interval_nat_ladder_c07621 n (by omega) (by omega)
      · -- n <= 5127781603859130497
        rcases Nat.lt_or_ge 5084472332115063821 n with h8 | h8
        · -- n > 5084472332115063821
          rcases Nat.lt_or_ge 5098867969762125179 n with h10 | h10
          · -- n > 5098867969762125179
            rcases Nat.lt_or_ge 5113304286336275801 n with h12 | h12
            · -- n > 5113304286336275801
              exact RamareSaouter2003.prime_interval_nat_ladder_c07620 n (by omega) (by omega)
            · -- n <= 5113304286336275801
              exact RamareSaouter2003.prime_interval_nat_ladder_c07619 n (by omega) (by omega)
          · -- n <= 5098867969762125179
            exact RamareSaouter2003.prime_interval_nat_ladder_c07618 n (by omega) (by omega)
        · -- n <= 5084472332115063821
          rcases Nat.lt_or_ge 5055802844318206913 n with h10 | h10
          · -- n > 5055802844318206913
            rcases Nat.lt_or_ge 5070117337030824443 n with h12 | h12
            · -- n > 5070117337030824443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07617 n (by omega) (by omega)
            · -- n <= 5070117337030824443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07616 n (by omega) (by omega)
          · -- n <= 5055802844318206913
            exact RamareSaouter2003.prime_interval_nat_ladder_c07615 n (by omega) (by omega)
  · -- n <= 5041528889912863657
    rcases Nat.lt_or_ge 4873351776020099033 n with h4 | h4
    · -- n > 4873351776020099033
      rcases Nat.lt_or_ge 4956726958903171477 n with h6 | h6
      · -- n > 4956726958903171477
        rcases Nat.lt_or_ge 4998947988777807587 n with h8 | h8
        · -- n > 4998947988777807587
          rcases Nat.lt_or_ge 5013101538150222091 n with h10 | h10
          · -- n > 5013101538150222091
            rcases Nat.lt_or_ge 5027295104675623457 n with h12 | h12
            · -- n > 5027295104675623457
              exact RamareSaouter2003.prime_interval_nat_ladder_c07614 n (by omega) (by omega)
            · -- n <= 5027295104675623457
              exact RamareSaouter2003.prime_interval_nat_ladder_c07613 n (by omega) (by omega)
          · -- n <= 5013101538150222091
            exact RamareSaouter2003.prime_interval_nat_ladder_c07612 n (by omega) (by omega)
        · -- n <= 4998947988777807587
          rcases Nat.lt_or_ge 4970760924540779077 n with h10 | h10
          · -- n > 4970760924540779077
            rcases Nat.lt_or_ge 4984834573113962113 n with h12 | h12
            · -- n > 4984834573113962113
              exact RamareSaouter2003.prime_interval_nat_ladder_c07611 n (by omega) (by omega)
            · -- n <= 4984834573113962113
              exact RamareSaouter2003.prime_interval_nat_ladder_c07610 n (by omega) (by omega)
          · -- n <= 4970760924540779077
            exact RamareSaouter2003.prime_interval_nat_ladder_c07609 n (by omega) (by omega)
      · -- n <= 4956726958903171477
        rcases Nat.lt_or_ge 4914862680786961921 n with h8 | h8
        · -- n > 4914862680786961921
          rcases Nat.lt_or_ge 4928777901097816273 n with h10 | h10
          · -- n > 4928777901097816273
            rcases Nat.lt_or_ge 4942732672592113873 n with h12 | h12
            · -- n > 4942732672592113873
              exact RamareSaouter2003.prime_interval_nat_ladder_c07608 n (by omega) (by omega)
            · -- n <= 4942732672592113873
              exact RamareSaouter2003.prime_interval_nat_ladder_c07607 n (by omega) (by omega)
          · -- n <= 4928777901097816273
            exact RamareSaouter2003.prime_interval_nat_ladder_c07606 n (by omega) (by omega)
        · -- n <= 4914862680786961921
          rcases Nat.lt_or_ge 4887149725317384647 n with h10 | h10
          · -- n > 4887149725317384647
            rcases Nat.lt_or_ge 4900986608433156079 n with h12 | h12
            · -- n > 4900986608433156079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07605 n (by omega) (by omega)
            · -- n <= 4900986608433156079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07604 n (by omega) (by omega)
          · -- n <= 4887149725317384647
            exact RamareSaouter2003.prime_interval_nat_ladder_c07603 n (by omega) (by omega)
    · -- n <= 4873351776020099033
      rcases Nat.lt_or_ge 4791378463081164001 n with h6 | h6
      · -- n > 4791378463081164001
        rcases Nat.lt_or_ge 4832191304097585511 n with h8 | h8
        · -- n > 4832191304097585511
          rcases Nat.lt_or_ge 4845872707424919347 n with h10 | h10
          · -- n > 4845872707424919347
            rcases Nat.lt_or_ge 4859592841686047557 n with h12 | h12
            · -- n > 4859592841686047557
              exact RamareSaouter2003.prime_interval_nat_ladder_c07602 n (by omega) (by omega)
            · -- n <= 4859592841686047557
              exact RamareSaouter2003.prime_interval_nat_ladder_c07601 n (by omega) (by omega)
          · -- n <= 4845872707424919347
            exact RamareSaouter2003.prime_interval_nat_ladder_c07600 n (by omega) (by omega)
        · -- n <= 4832191304097585511
          rcases Nat.lt_or_ge 4804944296629470739 n with h10 | h10
          · -- n > 4804944296629470739
            rcases Nat.lt_or_ge 4818548510157171707 n with h12 | h12
            · -- n > 4818548510157171707
              exact RamareSaouter2003.prime_interval_nat_ladder_c07599 n (by omega) (by omega)
            · -- n <= 4818548510157171707
              exact RamareSaouter2003.prime_interval_nat_ladder_c07598 n (by omega) (by omega)
          · -- n <= 4804944296629470739
            exact RamareSaouter2003.prime_interval_nat_ladder_c07597 n (by omega) (by omega)
      · -- n <= 4791378463081164001
        rcases Nat.lt_or_ge 4750910467328713921 n with h8 | h8
        · -- n > 4750910467328713921
          rcases Nat.lt_or_ge 4764361699591794217 n with h10 | h10
          · -- n > 4764361699591794217
            rcases Nat.lt_or_ge 4777850990018526991 n with h12 | h12
            · -- n > 4777850990018526991
              exact RamareSaouter2003.prime_interval_nat_ladder_c07596 n (by omega) (by omega)
            · -- n <= 4777850990018526991
              exact RamareSaouter2003.prime_interval_nat_ladder_c07595 n (by omega) (by omega)
          · -- n <= 4764361699591794217
            exact RamareSaouter2003.prime_interval_nat_ladder_c07594 n (by omega) (by omega)
        · -- n <= 4750910467328713921
          rcases Nat.lt_or_ge 4724122015954834501 n with h10 | h10
          · -- n > 4724122015954834501
            rcases Nat.lt_or_ge 4737497330260709041 n with h12 | h12
            · -- n > 4737497330260709041
              exact RamareSaouter2003.prime_interval_nat_ladder_c07593 n (by omega) (by omega)
            · -- n <= 4737497330260709041
              exact RamareSaouter2003.prime_interval_nat_ladder_c07592 n (by omega) (by omega)
          · -- n <= 4724122015954834501
            exact RamareSaouter2003.prime_interval_nat_ladder_c07591 n (by omega) (by omega)
