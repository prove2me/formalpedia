-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T21:33:37.785672+00:00
-- url     : https://prove2.me/submissions/5c290132-f1d4-4817-8742-556ed0efe396

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00650

theorem solution (n : Nat)
    (hn : 40472556721 < n) (hupper : n <= 45340845131) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 42836031331 n with h2 | h2
  · -- n > 42836031331
    rcases Nat.lt_or_ge 44020182641 n with h4 | h4
    · -- n > 44020182641
      rcases Nat.lt_or_ge 44624760161 n with h6 | h6
      · -- n > 44624760161
        rcases Nat.lt_or_ge 44930226811 n with h8 | h8
        · -- n > 44930226811
          rcases Nat.lt_or_ge 45135058433 n with h10 | h10
          · -- n > 45135058433
            rcases Nat.lt_or_ge 45237832121 n with h12 | h12
            · -- n > 45237832121
              exact RamareSaouter2003.prime_interval_nat_ladder_c00650 n (by omega) (by omega)
            · -- n <= 45237832121
              exact RamareSaouter2003.prime_interval_nat_ladder_c00649 n (by omega) (by omega)
          · -- n <= 45135058433
            rcases Nat.lt_or_ge 45032523511 n with h12 | h12
            · -- n > 45032523511
              exact RamareSaouter2003.prime_interval_nat_ladder_c00648 n (by omega) (by omega)
            · -- n <= 45032523511
              exact RamareSaouter2003.prime_interval_nat_ladder_c00647 n (by omega) (by omega)
        · -- n <= 44930226811
          rcases Nat.lt_or_ge 44726345693 n with h10 | h10
          · -- n > 44726345693
            rcases Nat.lt_or_ge 44828167729 n with h12 | h12
            · -- n > 44828167729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00646 n (by omega) (by omega)
            · -- n <= 44828167729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00645 n (by omega) (by omega)
          · -- n <= 44726345693
            exact RamareSaouter2003.prime_interval_nat_ladder_c00644 n (by omega) (by omega)
      · -- n <= 44624760161
        rcases Nat.lt_or_ge 44321417113 n with h8 | h8
        · -- n > 44321417113
          rcases Nat.lt_or_ge 44422296469 n with h10 | h10
          · -- n > 44422296469
            rcases Nat.lt_or_ge 44523410629 n with h12 | h12
            · -- n > 44523410629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00643 n (by omega) (by omega)
            · -- n <= 44523410629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00642 n (by omega) (by omega)
          · -- n <= 44422296469
            exact RamareSaouter2003.prime_interval_nat_ladder_c00641 n (by omega) (by omega)
        · -- n <= 44321417113
          rcases Nat.lt_or_ge 44120360789 n with h10 | h10
          · -- n > 44120360789
            rcases Nat.lt_or_ge 44220772087 n with h12 | h12
            · -- n > 44220772087
              exact RamareSaouter2003.prime_interval_nat_ladder_c00640 n (by omega) (by omega)
            · -- n <= 44220772087
              exact RamareSaouter2003.prime_interval_nat_ladder_c00639 n (by omega) (by omega)
          · -- n <= 44120360789
            exact RamareSaouter2003.prime_interval_nat_ladder_c00638 n (by omega) (by omega)
    · -- n <= 44020182641
      rcases Nat.lt_or_ge 43423979041 n with h6 | h6
      · -- n > 43423979041
        rcases Nat.lt_or_ge 43721041477 n with h8 | h8
        · -- n > 43721041477
          rcases Nat.lt_or_ge 43820523497 n with h10 | h10
          · -- n > 43820523497
            rcases Nat.lt_or_ge 43920237043 n with h12 | h12
            · -- n > 43920237043
              exact RamareSaouter2003.prime_interval_nat_ladder_c00637 n (by omega) (by omega)
            · -- n <= 43920237043
              exact RamareSaouter2003.prime_interval_nat_ladder_c00636 n (by omega) (by omega)
          · -- n <= 43820523497
            exact RamareSaouter2003.prime_interval_nat_ladder_c00635 n (by omega) (by omega)
        · -- n <= 43721041477
          rcases Nat.lt_or_ge 43522769777 n with h10 | h10
          · -- n > 43522769777
            rcases Nat.lt_or_ge 43621790437 n with h12 | h12
            · -- n > 43621790437
              exact RamareSaouter2003.prime_interval_nat_ladder_c00634 n (by omega) (by omega)
            · -- n <= 43621790437
              exact RamareSaouter2003.prime_interval_nat_ladder_c00633 n (by omega) (by omega)
          · -- n <= 43522769777
            exact RamareSaouter2003.prime_interval_nat_ladder_c00632 n (by omega) (by omega)
      · -- n <= 43423979041
        rcases Nat.lt_or_ge 43128980539 n with h8 | h8
        · -- n > 43128980539
          rcases Nat.lt_or_ge 43227084937 n with h10 | h10
          · -- n > 43227084937
            rcases Nat.lt_or_ge 43325417591 n with h12 | h12
            · -- n > 43325417591
              exact RamareSaouter2003.prime_interval_nat_ladder_c00631 n (by omega) (by omega)
            · -- n <= 43325417591
              exact RamareSaouter2003.prime_interval_nat_ladder_c00630 n (by omega) (by omega)
          · -- n <= 43227084937
            exact RamareSaouter2003.prime_interval_nat_ladder_c00629 n (by omega) (by omega)
        · -- n <= 43128980539
          rcases Nat.lt_or_ge 42933454331 n with h10 | h10
          · -- n > 42933454331
            rcases Nat.lt_or_ge 43031103781 n with h12 | h12
            · -- n > 43031103781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00628 n (by omega) (by omega)
            · -- n <= 43031103781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00627 n (by omega) (by omega)
          · -- n <= 42933454331
            exact RamareSaouter2003.prime_interval_nat_ladder_c00626 n (by omega) (by omega)
  · -- n <= 42836031331
    rcases Nat.lt_or_ge 41589911371 n with h4 | h4
    · -- n > 41589911371
      rcases Nat.lt_or_ge 42160370477 n with h6 | h6
      · -- n > 42160370477
        rcases Nat.lt_or_ge 42448594759 n with h8 | h8
        · -- n > 42448594759
          rcases Nat.lt_or_ge 42641863049 n with h10 | h10
          · -- n > 42641863049
            rcases Nat.lt_or_ge 42738834443 n with h12 | h12
            · -- n > 42738834443
              exact RamareSaouter2003.prime_interval_nat_ladder_c00625 n (by omega) (by omega)
            · -- n <= 42738834443
              exact RamareSaouter2003.prime_interval_nat_ladder_c00624 n (by omega) (by omega)
          · -- n <= 42641863049
            rcases Nat.lt_or_ge 42545116643 n with h12 | h12
            · -- n > 42545116643
              exact RamareSaouter2003.prime_interval_nat_ladder_c00623 n (by omega) (by omega)
            · -- n <= 42545116643
              exact RamareSaouter2003.prime_interval_nat_ladder_c00622 n (by omega) (by omega)
        · -- n <= 42448594759
          rcases Nat.lt_or_ge 42256222187 n with h10 | h10
          · -- n > 42256222187
            rcases Nat.lt_or_ge 42352296773 n with h12 | h12
            · -- n > 42352296773
              exact RamareSaouter2003.prime_interval_nat_ladder_c00621 n (by omega) (by omega)
            · -- n <= 42352296773
              exact RamareSaouter2003.prime_interval_nat_ladder_c00620 n (by omega) (by omega)
          · -- n <= 42256222187
            exact RamareSaouter2003.prime_interval_nat_ladder_c00619 n (by omega) (by omega)
      · -- n <= 42160370477
        rcases Nat.lt_or_ge 41874147437 n with h8 | h8
        · -- n > 41874147437
          rcases Nat.lt_or_ge 41969333669 n with h10 | h10
          · -- n > 41969333669
            rcases Nat.lt_or_ge 42064741127 n with h12 | h12
            · -- n > 42064741127
              exact RamareSaouter2003.prime_interval_nat_ladder_c00618 n (by omega) (by omega)
            · -- n <= 42064741127
              exact RamareSaouter2003.prime_interval_nat_ladder_c00617 n (by omega) (by omega)
          · -- n <= 41969333669
            exact RamareSaouter2003.prime_interval_nat_ladder_c00616 n (by omega) (by omega)
        · -- n <= 41874147437
          rcases Nat.lt_or_ge 41684436853 n with h10 | h10
          · -- n > 41684436853
            rcases Nat.lt_or_ge 41779182017 n with h12 | h12
            · -- n > 41779182017
              exact RamareSaouter2003.prime_interval_nat_ladder_c00615 n (by omega) (by omega)
            · -- n <= 41779182017
              exact RamareSaouter2003.prime_interval_nat_ladder_c00614 n (by omega) (by omega)
          · -- n <= 41684436853
            exact RamareSaouter2003.prime_interval_nat_ladder_c00613 n (by omega) (by omega)
    · -- n <= 41589911371
      rcases Nat.lt_or_ge 41027344093 n with h6 | h6
      · -- n > 41027344093
        rcases Nat.lt_or_ge 41307648337 n with h8 | h8
        · -- n > 41307648337
          rcases Nat.lt_or_ge 41401517719 n with h10 | h10
          · -- n > 41401517719
            rcases Nat.lt_or_ge 41495605219 n with h12 | h12
            · -- n > 41495605219
              exact RamareSaouter2003.prime_interval_nat_ladder_c00612 n (by omega) (by omega)
            · -- n <= 41495605219
              exact RamareSaouter2003.prime_interval_nat_ladder_c00611 n (by omega) (by omega)
          · -- n <= 41401517719
            exact RamareSaouter2003.prime_interval_nat_ladder_c00610 n (by omega) (by omega)
        · -- n <= 41307648337
          rcases Nat.lt_or_ge 41120561969 n with h10 | h10
          · -- n > 41120561969
            rcases Nat.lt_or_ge 41213996573 n with h12 | h12
            · -- n > 41213996573
              exact RamareSaouter2003.prime_interval_nat_ladder_c00609 n (by omega) (by omega)
            · -- n <= 41213996573
              exact RamareSaouter2003.prime_interval_nat_ladder_c00608 n (by omega) (by omega)
          · -- n <= 41120561969
            exact RamareSaouter2003.prime_interval_nat_ladder_c00607 n (by omega) (by omega)
      · -- n <= 41027344093
        rcases Nat.lt_or_ge 40748984833 n with h8 | h8
        · -- n > 40748984833
          rcases Nat.lt_or_ge 40841555981 n with h10 | h10
          · -- n > 40841555981
            rcases Nat.lt_or_ge 40934342257 n with h12 | h12
            · -- n > 40934342257
              exact RamareSaouter2003.prime_interval_nat_ladder_c00606 n (by omega) (by omega)
            · -- n <= 40934342257
              exact RamareSaouter2003.prime_interval_nat_ladder_c00605 n (by omega) (by omega)
          · -- n <= 40841555981
            exact RamareSaouter2003.prime_interval_nat_ladder_c00604 n (by omega) (by omega)
        · -- n <= 40748984833
          rcases Nat.lt_or_ge 40564485697 n with h10 | h10
          · -- n > 40564485697
            rcases Nat.lt_or_ge 40656628223 n with h12 | h12
            · -- n > 40656628223
              exact RamareSaouter2003.prime_interval_nat_ladder_c00603 n (by omega) (by omega)
            · -- n <= 40656628223
              exact RamareSaouter2003.prime_interval_nat_ladder_c00602 n (by omega) (by omega)
          · -- n <= 40564485697
            exact RamareSaouter2003.prime_interval_nat_ladder_c00601 n (by omega) (by omega)
