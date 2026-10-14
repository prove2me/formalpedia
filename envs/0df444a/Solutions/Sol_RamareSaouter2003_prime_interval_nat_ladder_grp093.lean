-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T11:52:43.548748+00:00
-- url     : https://prove2.me/submissions/b33fd9b2-26c5-4b88-8a21-a404941f7cb4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04650

theorem solution (n : Nat)
    (hn : 1004703773149963 < n) (hupper : n <= 1157209303635617) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1078263668072831 n with h2 | h2
  · -- n > 1078263668072831
    rcases Nat.lt_or_ge 1115462696236457 n with h4 | h4
    · -- n > 1115462696236457
      rcases Nat.lt_or_ge 1134541678499947 n with h6 | h6
      · -- n > 1134541678499947
        rcases Nat.lt_or_ge 1144202960667071 n with h8 | h8
        · -- n > 1144202960667071
          rcases Nat.lt_or_ge 1150687649654467 n with h10 | h10
          · -- n > 1150687649654467
            rcases Nat.lt_or_ge 1153942368246337 n with h12 | h12
            · -- n > 1153942368246337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04650 n (by omega) (by omega)
            · -- n <= 1153942368246337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04649 n (by omega) (by omega)
          · -- n <= 1150687649654467
            rcases Nat.lt_or_ge 1147441186333951 n with h12 | h12
            · -- n > 1147441186333951
              exact RamareSaouter2003.prime_interval_nat_ladder_c04648 n (by omega) (by omega)
            · -- n <= 1147441186333951
              exact RamareSaouter2003.prime_interval_nat_ladder_c04647 n (by omega) (by omega)
        · -- n <= 1144202960667071
          rcases Nat.lt_or_ge 1137753192904291 n with h10 | h10
          · -- n > 1137753192904291
            rcases Nat.lt_or_ge 1140973770617897 n with h12 | h12
            · -- n > 1140973770617897
              exact RamareSaouter2003.prime_interval_nat_ladder_c04646 n (by omega) (by omega)
            · -- n <= 1140973770617897
              exact RamareSaouter2003.prime_interval_nat_ladder_c04645 n (by omega) (by omega)
          · -- n <= 1137753192904291
            exact RamareSaouter2003.prime_interval_nat_ladder_c04644 n (by omega) (by omega)
      · -- n <= 1134541678499947
        rcases Nat.lt_or_ge 1124960060765201 n with h8 | h8
        · -- n > 1124960060765201
          rcases Nat.lt_or_ge 1128144963423697 n with h10 | h10
          · -- n > 1128144963423697
            rcases Nat.lt_or_ge 1131339076347521 n with h12 | h12
            · -- n > 1131339076347521
              exact RamareSaouter2003.prime_interval_nat_ladder_c04643 n (by omega) (by omega)
            · -- n <= 1131339076347521
              exact RamareSaouter2003.prime_interval_nat_ladder_c04642 n (by omega) (by omega)
          · -- n <= 1128144963423697
            exact RamareSaouter2003.prime_interval_nat_ladder_c04641 n (by omega) (by omega)
        · -- n <= 1124960060765201
          rcases Nat.lt_or_ge 1118620219302379 n with h10 | h10
          · -- n > 1118620219302379
            rcases Nat.lt_or_ge 1121784684351367 n with h12 | h12
            · -- n > 1121784684351367
              exact RamareSaouter2003.prime_interval_nat_ladder_c04640 n (by omega) (by omega)
            · -- n <= 1121784684351367
              exact RamareSaouter2003.prime_interval_nat_ladder_c04639 n (by omega) (by omega)
          · -- n <= 1118620219302379
            exact RamareSaouter2003.prime_interval_nat_ladder_c04638 n (by omega) (by omega)
    · -- n <= 1115462696236457
      rcases Nat.lt_or_ge 1096705839244607 n with h6 | h6
      · -- n > 1096705839244607
        rcases Nat.lt_or_ge 1106045431864169 n with h8 | h8
        · -- n > 1106045431864169
          rcases Nat.lt_or_ge 1109175886920631 n with h10 | h10
          · -- n > 1109175886920631
            rcases Nat.lt_or_ge 1112313767389417 n with h12 | h12
            · -- n > 1112313767389417
              exact RamareSaouter2003.prime_interval_nat_ladder_c04637 n (by omega) (by omega)
            · -- n <= 1112313767389417
              exact RamareSaouter2003.prime_interval_nat_ladder_c04636 n (by omega) (by omega)
          · -- n <= 1109175886920631
            exact RamareSaouter2003.prime_interval_nat_ladder_c04635 n (by omega) (by omega)
        · -- n <= 1106045431864169
          rcases Nat.lt_or_ge 1099809663264707 n with h10 | h10
          · -- n > 1099809663264707
            rcases Nat.lt_or_ge 1102923516711673 n with h12 | h12
            · -- n > 1102923516711673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04634 n (by omega) (by omega)
            · -- n <= 1102923516711673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04633 n (by omega) (by omega)
          · -- n <= 1099809663264707
            exact RamareSaouter2003.prime_interval_nat_ladder_c04632 n (by omega) (by omega)
      · -- n <= 1096705839244607
        rcases Nat.lt_or_ge 1087444432905221 n with h8 | h8
        · -- n > 1087444432905221
          rcases Nat.lt_or_ge 1090523043950567 n with h10 | h10
          · -- n > 1090523043950567
            rcases Nat.lt_or_ge 1093609710435211 n with h12 | h12
            · -- n > 1093609710435211
              exact RamareSaouter2003.prime_interval_nat_ladder_c04631 n (by omega) (by omega)
            · -- n <= 1093609710435211
              exact RamareSaouter2003.prime_interval_nat_ladder_c04630 n (by omega) (by omega)
          · -- n <= 1090523043950567
            exact RamareSaouter2003.prime_interval_nat_ladder_c04629 n (by omega) (by omega)
        · -- n <= 1087444432905221
          rcases Nat.lt_or_ge 1081314863692187 n with h10 | h10
          · -- n > 1081314863692187
            rcases Nat.lt_or_ge 1084374384676489 n with h12 | h12
            · -- n > 1084374384676489
              exact RamareSaouter2003.prime_interval_nat_ladder_c04628 n (by omega) (by omega)
            · -- n <= 1084374384676489
              exact RamareSaouter2003.prime_interval_nat_ladder_c04627 n (by omega) (by omega)
          · -- n <= 1081314863692187
            exact RamareSaouter2003.prime_interval_nat_ladder_c04626 n (by omega) (by omega)
  · -- n <= 1078263668072831
    rcases Nat.lt_or_ge 1039362111643183 n with h4 | h4
    · -- n > 1039362111643183
      rcases Nat.lt_or_ge 1057141625707681 n with h6 | h6
      · -- n > 1057141625707681
        rcases Nat.lt_or_ge 1066142026779581 n with h8 | h8
        · -- n > 1066142026779581
          rcases Nat.lt_or_ge 1072185409876363 n with h10 | h10
          · -- n > 1072185409876363
            rcases Nat.lt_or_ge 1075220063622437 n with h12 | h12
            · -- n > 1075220063622437
              exact RamareSaouter2003.prime_interval_nat_ladder_c04625 n (by omega) (by omega)
            · -- n <= 1075220063622437
              exact RamareSaouter2003.prime_interval_nat_ladder_c04624 n (by omega) (by omega)
          · -- n <= 1072185409876363
            rcases Nat.lt_or_ge 1069159033937003 n with h12 | h12
            · -- n > 1069159033937003
              exact RamareSaouter2003.prime_interval_nat_ladder_c04623 n (by omega) (by omega)
            · -- n <= 1069159033937003
              exact RamareSaouter2003.prime_interval_nat_ladder_c04622 n (by omega) (by omega)
        · -- n <= 1066142026779581
          rcases Nat.lt_or_ge 1060134351442063 n with h10 | h10
          · -- n > 1060134351442063
            rcases Nat.lt_or_ge 1063133851266337 n with h12 | h12
            · -- n > 1063133851266337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04621 n (by omega) (by omega)
            · -- n <= 1063133851266337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04620 n (by omega) (by omega)
          · -- n <= 1060134351442063
            exact RamareSaouter2003.prime_interval_nat_ladder_c04619 n (by omega) (by omega)
      · -- n <= 1057141625707681
        rcases Nat.lt_or_ge 1048215053355653 n with h8 | h8
        · -- n > 1048215053355653
          rcases Nat.lt_or_ge 1051182805748857 n with h10 | h10
          · -- n > 1051182805748857
            rcases Nat.lt_or_ge 1054158584001197 n with h12 | h12
            · -- n > 1054158584001197
              exact RamareSaouter2003.prime_interval_nat_ladder_c04618 n (by omega) (by omega)
            · -- n <= 1054158584001197
              exact RamareSaouter2003.prime_interval_nat_ladder_c04617 n (by omega) (by omega)
          · -- n <= 1051182805748857
            exact RamareSaouter2003.prime_interval_nat_ladder_c04616 n (by omega) (by omega)
        · -- n <= 1048215053355653
          rcases Nat.lt_or_ge 1042304788113079 n with h10 | h10
          · -- n > 1042304788113079
            rcases Nat.lt_or_ge 1045255697928943 n with h12 | h12
            · -- n > 1045255697928943
              exact RamareSaouter2003.prime_interval_nat_ladder_c04615 n (by omega) (by omega)
            · -- n <= 1045255697928943
              exact RamareSaouter2003.prime_interval_nat_ladder_c04614 n (by omega) (by omega)
          · -- n <= 1042304788113079
            exact RamareSaouter2003.prime_interval_nat_ladder_c04613 n (by omega) (by omega)
    · -- n <= 1039362111643183
      rcases Nat.lt_or_ge 1021886242023989 n with h6 | h6
      · -- n > 1021886242023989
        rcases Nat.lt_or_ge 1030587872465429 n with h8 | h8
        · -- n > 1030587872465429
          rcases Nat.lt_or_ge 1033505570006849 n with h10 | h10
          · -- n > 1033505570006849
            rcases Nat.lt_or_ge 1036431324033407 n with h12 | h12
            · -- n > 1036431324033407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04612 n (by omega) (by omega)
            · -- n <= 1036431324033407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04611 n (by omega) (by omega)
          · -- n <= 1033505570006849
            exact RamareSaouter2003.prime_interval_nat_ladder_c04610 n (by omega) (by omega)
        · -- n <= 1030587872465429
          rcases Nat.lt_or_ge 1024777777535179 n with h10 | h10
          · -- n > 1024777777535179
            rcases Nat.lt_or_ge 1027678721194417 n with h12 | h12
            · -- n > 1027678721194417
              exact RamareSaouter2003.prime_interval_nat_ladder_c04609 n (by omega) (by omega)
            · -- n <= 1027678721194417
              exact RamareSaouter2003.prime_interval_nat_ladder_c04608 n (by omega) (by omega)
          · -- n <= 1024777777535179
            exact RamareSaouter2003.prime_interval_nat_ladder_c04607 n (by omega) (by omega)
      · -- n <= 1021886242023989
        rcases Nat.lt_or_ge 1013259003993473 n with h8 | h8
        · -- n > 1013259003993473
          rcases Nat.lt_or_ge 1016126266445221 n with h10 | h10
          · -- n > 1016126266445221
            rcases Nat.lt_or_ge 1019001794097113 n with h12 | h12
            · -- n > 1019001794097113
              exact RamareSaouter2003.prime_interval_nat_ladder_c04606 n (by omega) (by omega)
            · -- n <= 1019001794097113
              exact RamareSaouter2003.prime_interval_nat_ladder_c04605 n (by omega) (by omega)
          · -- n <= 1016126266445221
            exact RamareSaouter2003.prime_interval_nat_ladder_c04604 n (by omega) (by omega)
        · -- n <= 1013259003993473
          rcases Nat.lt_or_ge 1007547549088921 n with h10 | h10
          · -- n > 1007547549088921
            rcases Nat.lt_or_ge 1010399223997321 n with h12 | h12
            · -- n > 1010399223997321
              exact RamareSaouter2003.prime_interval_nat_ladder_c04603 n (by omega) (by omega)
            · -- n <= 1010399223997321
              exact RamareSaouter2003.prime_interval_nat_ladder_c04602 n (by omega) (by omega)
          · -- n <= 1007547549088921
            exact RamareSaouter2003.prime_interval_nat_ladder_c04601 n (by omega) (by omega)
