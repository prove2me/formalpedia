-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:04:57.956208+00:00
-- url     : https://prove2.me/submissions/393192a2-11b0-47ba-92d7-029e966666c0

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08750
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08766

theorem solution (n : Nat)
    (hn : 88937429173397375471 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 94305118248471178847 n with h2 | h2
  · -- n > 94305118248471178847
    rcases Nat.lt_or_ge 97109253083730406543 n with h4 | h4
    · -- n > 97109253083730406543
      rcases Nat.lt_or_ge 98542435794570445589 n with h6 | h6
      · -- n > 98542435794570445589
        rcases Nat.lt_or_ge 99266939396778419291 n with h8 | h8
        · -- n > 99266939396778419291
          rcases Nat.lt_or_ge 99752898761777419393 n with h10 | h10
          · -- n > 99752898761777419393
            rcases Nat.lt_or_ge 99876372021712761067 n with h12 | h12
            · -- n > 99876372021712761067
              exact RamareSaouter2003.prime_interval_nat_ladder_c08766 n (by omega) hupper
            · -- n <= 99876372021712761067
              exact RamareSaouter2003.prime_interval_nat_ladder_c08765 n (by omega) (by omega)
          · -- n <= 99752898761777419393
            rcases Nat.lt_or_ge 99509622548796803389 n with h12 | h12
            · -- n > 99509622548796803389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08764 n (by omega) (by omega)
            · -- n <= 99509622548796803389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08763 n (by omega) (by omega)
        · -- n <= 99266939396778419291
          rcases Nat.lt_or_ge 98783347477968144821 n with h10 | h10
          · -- n > 98783347477968144821
            rcases Nat.lt_or_ge 99024848122048181101 n with h12 | h12
            · -- n > 99024848122048181101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08762 n (by omega) (by omega)
            · -- n <= 99024848122048181101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08761 n (by omega) (by omega)
          · -- n <= 98783347477968144821
            exact RamareSaouter2003.prime_interval_nat_ladder_c08760 n (by omega) (by omega)
      · -- n <= 98542435794570445589
        rcases Nat.lt_or_ge 97823220264373199801 n with h8 | h8
        · -- n > 97823220264373199801
          rcases Nat.lt_or_ge 98062373735464130533 n with h10 | h10
          · -- n > 98062373735464130533
            rcases Nat.lt_or_ge 98302111571158819661 n with h12 | h12
            · -- n > 98302111571158819661
              exact RamareSaouter2003.prime_interval_nat_ladder_c08759 n (by omega) (by omega)
            · -- n <= 98302111571158819661
              exact RamareSaouter2003.prime_interval_nat_ladder_c08758 n (by omega) (by omega)
          · -- n <= 98062373735464130533
            exact RamareSaouter2003.prime_interval_nat_ladder_c08757 n (by omega) (by omega)
        · -- n <= 97823220264373199801
          rcases Nat.lt_or_ge 97346661249771540223 n with h10 | h10
          · -- n > 97346661249771540223
            rcases Nat.lt_or_ge 97584649848949642019 n with h12 | h12
            · -- n > 97584649848949642019
              exact RamareSaouter2003.prime_interval_nat_ladder_c08756 n (by omega) (by omega)
            · -- n <= 97584649848949642019
              exact RamareSaouter2003.prime_interval_nat_ladder_c08755 n (by omega) (by omega)
          · -- n <= 97346661249771540223
            exact RamareSaouter2003.prime_interval_nat_ladder_c08754 n (by omega) (by omega)
    · -- n <= 97109253083730406543
      rcases Nat.lt_or_ge 95696914790496772393 n with h6 | h6
      · -- n > 95696914790496772393
        rcases Nat.lt_or_ge 96400497229495954519 n with h8 | h8
        · -- n > 96400497229495954519
          rcases Nat.lt_or_ge 96636172683614035291 n with h10 | h10
          · -- n > 96636172683614035291
            rcases Nat.lt_or_ge 96872424171275901283 n with h12 | h12
            · -- n > 96872424171275901283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08753 n (by omega) (by omega)
            · -- n <= 96872424171275901283
              exact RamareSaouter2003.prime_interval_nat_ladder_c08752 n (by omega) (by omega)
          · -- n <= 96636172683614035291
            exact RamareSaouter2003.prime_interval_nat_ladder_c08751 n (by omega) (by omega)
        · -- n <= 96400497229495954519
          rcases Nat.lt_or_ge 95930869688994395017 n with h10 | h10
          · -- n > 95930869688994395017
            rcases Nat.lt_or_ge 96165396760492908073 n with h12 | h12
            · -- n > 96165396760492908073
              exact RamareSaouter2003.prime_interval_nat_ladder_c08750 n (by omega) (by omega)
            · -- n <= 96165396760492908073
              exact RamareSaouter2003.prime_interval_nat_ladder_c08749 n (by omega) (by omega)
          · -- n <= 95930869688994395017
            exact RamareSaouter2003.prime_interval_nat_ladder_c08748 n (by omega) (by omega)
      · -- n <= 95696914790496772393
        rcases Nat.lt_or_ge 94998466864881155923 n with h8 | h8
        · -- n > 94998466864881155923
          rcases Nat.lt_or_ge 95230714460734374173 n with h10 | h10
          · -- n > 95230714460734374173
            rcases Nat.lt_or_ge 95463530023860135101 n with h12 | h12
            · -- n > 95463530023860135101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08747 n (by omega) (by omega)
            · -- n <= 95463530023860135101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08746 n (by omega) (by omega)
          · -- n <= 95230714460734374173
            exact RamareSaouter2003.prime_interval_nat_ladder_c08745 n (by omega) (by omega)
        · -- n <= 94998466864881155923
          rcases Nat.lt_or_ge 94535670718695131557 n with h10 | h10
          · -- n > 94535670718695131557
            rcases Nat.lt_or_ge 94766785767208000361 n with h12 | h12
            · -- n > 94766785767208000361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08744 n (by omega) (by omega)
            · -- n <= 94766785767208000361
              exact RamareSaouter2003.prime_interval_nat_ladder_c08743 n (by omega) (by omega)
          · -- n <= 94535670718695131557
            exact RamareSaouter2003.prime_interval_nat_ladder_c08742 n (by omega) (by omega)
  · -- n <= 94305118248471178847
    rcases Nat.lt_or_ge 91581957525108451529 n with h4 | h4
    · -- n > 91581957525108451529
      rcases Nat.lt_or_ge 92933563482995182691 n with h6 | h6
      · -- n > 92933563482995182691
        rcases Nat.lt_or_ge 93616829181789735763 n with h8 | h8
        · -- n > 93616829181789735763
          rcases Nat.lt_or_ge 93845698625019245351 n with h10 | h10
          · -- n > 93845698625019245351
            rcases Nat.lt_or_ge 94075128165161234603 n with h12 | h12
            · -- n > 94075128165161234603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08741 n (by omega) (by omega)
            · -- n <= 94075128165161234603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08740 n (by omega) (by omega)
          · -- n <= 93845698625019245351
            exact RamareSaouter2003.prime_interval_nat_ladder_c08739 n (by omega) (by omega)
        · -- n <= 93616829181789735763
          rcases Nat.lt_or_ge 93160763056728324553 n with h10 | h10
          · -- n > 93160763056728324553
            rcases Nat.lt_or_ge 93388517809293514583 n with h12 | h12
            · -- n > 93388517809293514583
              exact RamareSaouter2003.prime_interval_nat_ladder_c08738 n (by omega) (by omega)
            · -- n <= 93388517809293514583
              exact RamareSaouter2003.prime_interval_nat_ladder_c08737 n (by omega) (by omega)
          · -- n <= 93160763056728324553
            exact RamareSaouter2003.prime_interval_nat_ladder_c08736 n (by omega) (by omega)
      · -- n <= 92933563482995182691
        rcases Nat.lt_or_ge 92255285225021443309 n with h8 | h8
        · -- n > 92255285225021443309
          rcases Nat.lt_or_ge 92480826560979883921 n with h10 | h10
          · -- n > 92480826560979883921
            rcases Nat.lt_or_ge 92706918766046094373 n with h12 | h12
            · -- n > 92706918766046094373
              exact RamareSaouter2003.prime_interval_nat_ladder_c08735 n (by omega) (by omega)
            · -- n <= 92706918766046094373
              exact RamareSaouter2003.prime_interval_nat_ladder_c08734 n (by omega) (by omega)
          · -- n <= 92480826560979883921
            exact RamareSaouter2003.prime_interval_nat_ladder_c08733 n (by omega) (by omega)
        · -- n <= 92255285225021443309
          rcases Nat.lt_or_ge 91805852796063435089 n with h10 | h10
          · -- n > 91805852796063435089
            rcases Nat.lt_or_ge 92030294516501525581 n with h12 | h12
            · -- n > 92030294516501525581
              exact RamareSaouter2003.prime_interval_nat_ladder_c08732 n (by omega) (by omega)
            · -- n <= 92030294516501525581
              exact RamareSaouter2003.prime_interval_nat_ladder_c08731 n (by omega) (by omega)
          · -- n <= 91805852796063435089
            exact RamareSaouter2003.prime_interval_nat_ladder_c08730 n (by omega) (by omega)
    · -- n <= 91581957525108451529
      rcases Nat.lt_or_ge 90250006425355035139 n with h6 | h6
      · -- n > 90250006425355035139
        rcases Nat.lt_or_ge 90913543011317448349 n with h8 | h8
        · -- n > 90913543011317448349
          rcases Nat.lt_or_ge 91135803888706390739 n with h10 | h10
          · -- n > 91135803888706390739
            rcases Nat.lt_or_ge 91358608260899830933 n with h12 | h12
            · -- n > 91358608260899830933
              exact RamareSaouter2003.prime_interval_nat_ladder_c08729 n (by omega) (by omega)
            · -- n <= 91358608260899830933
              exact RamareSaouter2003.prime_interval_nat_ladder_c08728 n (by omega) (by omega)
          · -- n <= 91135803888706390739
            exact RamareSaouter2003.prime_interval_nat_ladder_c08727 n (by omega) (by omega)
        · -- n <= 90913543011317448349
          rcases Nat.lt_or_ge 90470645440412915501 n with h10 | h10
          · -- n > 90470645440412915501
            rcases Nat.lt_or_ge 90691823852163951689 n with h12 | h12
            · -- n > 90691823852163951689
              exact RamareSaouter2003.prime_interval_nat_ladder_c08726 n (by omega) (by omega)
            · -- n <= 90691823852163951689
              exact RamareSaouter2003.prime_interval_nat_ladder_c08725 n (by omega) (by omega)
          · -- n <= 90470645440412915501
            exact RamareSaouter2003.prime_interval_nat_ladder_c08724 n (by omega) (by omega)
      · -- n <= 90250006425355035139
        rcases Nat.lt_or_ge 89591313219577037569 n with h8 | h8
        · -- n > 89591313219577037569
          rcases Nat.lt_or_ge 89810341876291006093 n with h10 | h10
          · -- n > 89810341876291006093
            rcases Nat.lt_or_ge 90029905798653501217 n with h12 | h12
            · -- n > 90029905798653501217
              exact RamareSaouter2003.prime_interval_nat_ladder_c08723 n (by omega) (by omega)
            · -- n <= 90029905798653501217
              exact RamareSaouter2003.prime_interval_nat_ladder_c08722 n (by omega) (by omega)
          · -- n <= 89810341876291006093
            exact RamareSaouter2003.prime_interval_nat_ladder_c08721 n (by omega) (by omega)
        · -- n <= 89591313219577037569
          rcases Nat.lt_or_ge 89154858940607145193 n with h10 | h10
          · -- n > 89154858940607145193
            rcases Nat.lt_or_ge 89372819302109948653 n with h12 | h12
            · -- n > 89372819302109948653
              exact RamareSaouter2003.prime_interval_nat_ladder_c08720 n (by omega) (by omega)
            · -- n <= 89372819302109948653
              exact RamareSaouter2003.prime_interval_nat_ladder_c08719 n (by omega) (by omega)
          · -- n <= 89154858940607145193
            exact RamareSaouter2003.prime_interval_nat_ladder_c08718 n (by omega) (by omega)
