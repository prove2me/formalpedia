-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T12:04:02.831822+00:00
-- url     : https://prove2.me/submissions/f33ef964-3db3-45b4-8605-a17b5d216113

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04700

theorem solution (n : Nat)
    (hn : 1157209303635617 < n) (hupper : n <= 1332869397939077) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1241940703469813 n with h2 | h2
  · -- n > 1241940703469813
    rcases Nat.lt_or_ge 1284781008832913 n with h4 | h4
    · -- n > 1284781008832913
      rcases Nat.lt_or_ge 1306758151578409 n with h6 | h6
      · -- n > 1306758151578409
        rcases Nat.lt_or_ge 1317886169203421 n with h8 | h8
        · -- n > 1317886169203421
          rcases Nat.lt_or_ge 1325356419741619 n with h10 | h10
          · -- n > 1325356419741619
            rcases Nat.lt_or_ge 1329108760412747 n with h12 | h12
            · -- n > 1329108760412747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04700 n (by omega) (by omega)
            · -- n <= 1329108760412747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04699 n (by omega) (by omega)
          · -- n <= 1325356419741619
            rcases Nat.lt_or_ge 1321617384088879 n with h12 | h12
            · -- n > 1321617384088879
              exact RamareSaouter2003.prime_interval_nat_ladder_c04698 n (by omega) (by omega)
            · -- n <= 1321617384088879
              exact RamareSaouter2003.prime_interval_nat_ladder_c04697 n (by omega) (by omega)
        · -- n <= 1317886169203421
          rcases Nat.lt_or_ge 1310457155181371 n with h10 | h10
          · -- n > 1310457155181371
            rcases Nat.lt_or_ge 1314166101037483 n with h12 | h12
            · -- n > 1314166101037483
              exact RamareSaouter2003.prime_interval_nat_ladder_c04696 n (by omega) (by omega)
            · -- n <= 1314166101037483
              exact RamareSaouter2003.prime_interval_nat_ladder_c04695 n (by omega) (by omega)
          · -- n <= 1310457155181371
            exact RamareSaouter2003.prime_interval_nat_ladder_c04694 n (by omega) (by omega)
      · -- n <= 1306758151578409
        rcases Nat.lt_or_ge 1295722309562497 n with h8 | h8
        · -- n > 1295722309562497
          rcases Nat.lt_or_ge 1299390750647177 n with h10 | h10
          · -- n > 1299390750647177
            rcases Nat.lt_or_ge 1303068779037661 n with h12 | h12
            · -- n > 1303068779037661
              exact RamareSaouter2003.prime_interval_nat_ladder_c04693 n (by omega) (by omega)
            · -- n <= 1303068779037661
              exact RamareSaouter2003.prime_interval_nat_ladder_c04692 n (by omega) (by omega)
          · -- n <= 1299390750647177
            exact RamareSaouter2003.prime_interval_nat_ladder_c04691 n (by omega) (by omega)
        · -- n <= 1295722309562497
          rcases Nat.lt_or_ge 1288416637032131 n with h10 | h10
          · -- n > 1288416637032131
            rcases Nat.lt_or_ge 1292064377094847 n with h12 | h12
            · -- n > 1292064377094847
              exact RamareSaouter2003.prime_interval_nat_ladder_c04690 n (by omega) (by omega)
            · -- n <= 1292064377094847
              exact RamareSaouter2003.prime_interval_nat_ladder_c04689 n (by omega) (by omega)
          · -- n <= 1288416637032131
            exact RamareSaouter2003.prime_interval_nat_ladder_c04688 n (by omega) (by omega)
    · -- n <= 1284781008832913
      rcases Nat.lt_or_ge 1263178107892307 n with h6 | h6
      · -- n > 1263178107892307
        rcases Nat.lt_or_ge 1273933213563121 n with h8 | h8
        · -- n > 1273933213563121
          rcases Nat.lt_or_ge 1277539603392781 n with h10 | h10
          · -- n > 1277539603392781
            rcases Nat.lt_or_ge 1281154455288217 n with h12 | h12
            · -- n > 1281154455288217
              exact RamareSaouter2003.prime_interval_nat_ladder_c04687 n (by omega) (by omega)
            · -- n <= 1281154455288217
              exact RamareSaouter2003.prime_interval_nat_ladder_c04686 n (by omega) (by omega)
          · -- n <= 1277539603392781
            exact RamareSaouter2003.prime_interval_nat_ladder_c04685 n (by omega) (by omega)
        · -- n <= 1273933213563121
          rcases Nat.lt_or_ge 1266752952385247 n with h10 | h10
          · -- n > 1266752952385247
            rcases Nat.lt_or_ge 1270337838484853 n with h12 | h12
            · -- n > 1270337838484853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04684 n (by omega) (by omega)
            · -- n <= 1270337838484853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04683 n (by omega) (by omega)
          · -- n <= 1266752952385247
            exact RamareSaouter2003.prime_interval_nat_ladder_c04682 n (by omega) (by omega)
      · -- n <= 1263178107892307
        rcases Nat.lt_or_ge 1252513255471493 n with h8 | h8
        · -- n > 1252513255471493
          rcases Nat.lt_or_ge 1256058035166523 n with h10 | h10
          · -- n > 1256058035166523
            rcases Nat.lt_or_ge 1259612149323169 n with h12 | h12
            · -- n > 1259612149323169
              exact RamareSaouter2003.prime_interval_nat_ladder_c04681 n (by omega) (by omega)
            · -- n <= 1259612149323169
              exact RamareSaouter2003.prime_interval_nat_ladder_c04680 n (by omega) (by omega)
          · -- n <= 1256058035166523
            exact RamareSaouter2003.prime_interval_nat_ladder_c04679 n (by omega) (by omega)
        · -- n <= 1252513255471493
          rcases Nat.lt_or_ge 1245455674591451 n with h10 | h10
          · -- n > 1245455674591451
            rcases Nat.lt_or_ge 1248981480309083 n with h12 | h12
            · -- n > 1248981480309083
              exact RamareSaouter2003.prime_interval_nat_ladder_c04678 n (by omega) (by omega)
            · -- n <= 1248981480309083
              exact RamareSaouter2003.prime_interval_nat_ladder_c04677 n (by omega) (by omega)
          · -- n <= 1245455674591451
            exact RamareSaouter2003.prime_interval_nat_ladder_c04676 n (by omega) (by omega)
  · -- n <= 1241940703469813
    rcases Nat.lt_or_ge 1197134337814763 n with h4 | h4
    · -- n > 1197134337814763
      rcases Nat.lt_or_ge 1217609459740801 n with h6 | h6
      · -- n > 1217609459740801
        rcases Nat.lt_or_ge 1227979617856279 n with h8 | h8
        · -- n > 1227979617856279
          rcases Nat.lt_or_ge 1234939999107407 n with h10 | h10
          · -- n > 1234939999107407
            rcases Nat.lt_or_ge 1238435202910627 n with h12 | h12
            · -- n > 1238435202910627
              exact RamareSaouter2003.prime_interval_nat_ladder_c04675 n (by omega) (by omega)
            · -- n <= 1238435202910627
              exact RamareSaouter2003.prime_interval_nat_ladder_c04674 n (by omega) (by omega)
          · -- n <= 1234939999107407
            rcases Nat.lt_or_ge 1231455278366147 n with h12 | h12
            · -- n > 1231455278366147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04673 n (by omega) (by omega)
            · -- n <= 1231455278366147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04672 n (by omega) (by omega)
        · -- n <= 1227979617856279
          rcases Nat.lt_or_ge 1221056378281951 n with h10 | h10
          · -- n > 1221056378281951
            rcases Nat.lt_or_ge 1224512783861651 n with h12 | h12
            · -- n > 1224512783861651
              exact RamareSaouter2003.prime_interval_nat_ladder_c04671 n (by omega) (by omega)
            · -- n <= 1224512783861651
              exact RamareSaouter2003.prime_interval_nat_ladder_c04670 n (by omega) (by omega)
          · -- n <= 1221056378281951
            exact RamareSaouter2003.prime_interval_nat_ladder_c04669 n (by omega) (by omega)
      · -- n <= 1217609459740801
        rcases Nat.lt_or_ge 1207328653661149 n with h8 | h8
        · -- n > 1207328653661149
          rcases Nat.lt_or_ge 1210745549396897 n with h10 | h10
          · -- n > 1210745549396897
            rcases Nat.lt_or_ge 1214172083114513 n with h12 | h12
            · -- n > 1214172083114513
              exact RamareSaouter2003.prime_interval_nat_ladder_c04668 n (by omega) (by omega)
            · -- n <= 1214172083114513
              exact RamareSaouter2003.prime_interval_nat_ladder_c04667 n (by omega) (by omega)
          · -- n <= 1210745549396897
            exact RamareSaouter2003.prime_interval_nat_ladder_c04666 n (by omega) (by omega)
        · -- n <= 1207328653661149
          rcases Nat.lt_or_ge 1200523484006251 n with h10 | h10
          · -- n > 1200523484006251
            rcases Nat.lt_or_ge 1203921373892669 n with h12 | h12
            · -- n > 1203921373892669
              exact RamareSaouter2003.prime_interval_nat_ladder_c04665 n (by omega) (by omega)
            · -- n <= 1203921373892669
              exact RamareSaouter2003.prime_interval_nat_ladder_c04664 n (by omega) (by omega)
          · -- n <= 1200523484006251
            exact RamareSaouter2003.prime_interval_nat_ladder_c04663 n (by omega) (by omega)
    · -- n <= 1197134337814763
      rcases Nat.lt_or_ge 1177004638634731 n with h6 | h6
      · -- n > 1177004638634731
        rcases Nat.lt_or_ge 1187028653760953 n with h8 | h8
        · -- n > 1187028653760953
          rcases Nat.lt_or_ge 1190389465919389 n with h10 | h10
          · -- n > 1190389465919389
            rcases Nat.lt_or_ge 1193756409357839 n with h12 | h12
            · -- n > 1193756409357839
              exact RamareSaouter2003.prime_interval_nat_ladder_c04662 n (by omega) (by omega)
            · -- n <= 1193756409357839
              exact RamareSaouter2003.prime_interval_nat_ladder_c04661 n (by omega) (by omega)
          · -- n <= 1190389465919389
            exact RamareSaouter2003.prime_interval_nat_ladder_c04660 n (by omega) (by omega)
        · -- n <= 1187028653760953
          rcases Nat.lt_or_ge 1180336123380959 n with h10 | h10
          · -- n > 1180336123380959
            rcases Nat.lt_or_ge 1183677406740187 n with h12 | h12
            · -- n > 1183677406740187
              exact RamareSaouter2003.prime_interval_nat_ladder_c04659 n (by omega) (by omega)
            · -- n <= 1183677406740187
              exact RamareSaouter2003.prime_interval_nat_ladder_c04658 n (by omega) (by omega)
          · -- n <= 1180336123380959
            exact RamareSaouter2003.prime_interval_nat_ladder_c04657 n (by omega) (by omega)
      · -- n <= 1177004638634731
        rcases Nat.lt_or_ge 1167065489377979 n with h8 | h8
        · -- n > 1167065489377979
          rcases Nat.lt_or_ge 1170369272146049 n with h10 | h10
          · -- n > 1170369272146049
            rcases Nat.lt_or_ge 1173682316191361 n with h12 | h12
            · -- n > 1173682316191361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04656 n (by omega) (by omega)
            · -- n <= 1173682316191361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04655 n (by omega) (by omega)
          · -- n <= 1170369272146049
            exact RamareSaouter2003.prime_interval_nat_ladder_c04654 n (by omega) (by omega)
        · -- n <= 1167065489377979
          rcases Nat.lt_or_ge 1160485216693091 n with h10 | h10
          · -- n > 1160485216693091
            rcases Nat.lt_or_ge 1163770742852141 n with h12 | h12
            · -- n > 1163770742852141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04653 n (by omega) (by omega)
            · -- n <= 1163770742852141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04652 n (by omega) (by omega)
          · -- n <= 1160485216693091
            exact RamareSaouter2003.prime_interval_nat_ladder_c04651 n (by omega) (by omega)
