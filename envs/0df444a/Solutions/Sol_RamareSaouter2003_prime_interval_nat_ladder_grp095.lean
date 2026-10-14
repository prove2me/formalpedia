-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T12:30:01.276256+00:00
-- url     : https://prove2.me/submissions/8b8dc86f-a53c-4529-96da-355a61fd6496

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04750

theorem solution (n : Nat)
    (hn : 1332869397939077 < n) (hupper : n <= 1535198451695543) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1430466675481579 n with h2 | h2
  · -- n > 1430466675481579
    rcases Nat.lt_or_ge 1479817157466407 n with h4 | h4
    · -- n > 1479817157466407
      rcases Nat.lt_or_ge 1505126016677573 n with h6 | h6
      · -- n > 1505126016677573
        rcases Nat.lt_or_ge 1517939544424103 n with h8 | h8
        · -- n > 1517939544424103
          rcases Nat.lt_or_ge 1526545276418761 n with h10 | h10
          · -- n > 1526545276418761
            rcases Nat.lt_or_ge 1530866695036253 n with h12 | h12
            · -- n > 1530866695036253
              exact RamareSaouter2003.prime_interval_nat_ladder_c04750 n (by omega) (by omega)
            · -- n <= 1530866695036253
              exact RamareSaouter2003.prime_interval_nat_ladder_c04749 n (by omega) (by omega)
          · -- n <= 1526545276418761
            rcases Nat.lt_or_ge 1522236833520181 n with h12 | h12
            · -- n > 1522236833520181
              exact RamareSaouter2003.prime_interval_nat_ladder_c04748 n (by omega) (by omega)
            · -- n <= 1522236833520181
              exact RamareSaouter2003.prime_interval_nat_ladder_c04747 n (by omega) (by omega)
        · -- n <= 1517939544424103
          rcases Nat.lt_or_ge 1509387430400621 n with h10 | h10
          · -- n > 1509387430400621
            rcases Nat.lt_or_ge 1513653925722121 n with h12 | h12
            · -- n > 1513653925722121
              exact RamareSaouter2003.prime_interval_nat_ladder_c04746 n (by omega) (by omega)
            · -- n <= 1513653925722121
              exact RamareSaouter2003.prime_interval_nat_ladder_c04745 n (by omega) (by omega)
          · -- n <= 1509387430400621
            exact RamareSaouter2003.prime_interval_nat_ladder_c04744 n (by omega) (by omega)
      · -- n <= 1505126016677573
        rcases Nat.lt_or_ge 1492418031724031 n with h8 | h8
        · -- n > 1492418031724031
          rcases Nat.lt_or_ge 1496642314108993 n with h10 | h10
          · -- n > 1496642314108993
            rcases Nat.lt_or_ge 1500878067184877 n with h12 | h12
            · -- n > 1500878067184877
              exact RamareSaouter2003.prime_interval_nat_ladder_c04743 n (by omega) (by omega)
            · -- n <= 1500878067184877
              exact RamareSaouter2003.prime_interval_nat_ladder_c04742 n (by omega) (by omega)
          · -- n <= 1496642314108993
            exact RamareSaouter2003.prime_interval_nat_ladder_c04741 n (by omega) (by omega)
        · -- n <= 1492418031724031
          rcases Nat.lt_or_ge 1484004320944487 n with h10 | h10
          · -- n > 1484004320944487
            rcases Nat.lt_or_ge 1488205115395753 n with h12 | h12
            · -- n > 1488205115395753
              exact RamareSaouter2003.prime_interval_nat_ladder_c04740 n (by omega) (by omega)
            · -- n <= 1488205115395753
              exact RamareSaouter2003.prime_interval_nat_ladder_c04739 n (by omega) (by omega)
          · -- n <= 1484004320944487
            exact RamareSaouter2003.prime_interval_nat_ladder_c04738 n (by omega) (by omega)
    · -- n <= 1479817157466407
      rcases Nat.lt_or_ge 1454931222502621 n with h6 | h6
      · -- n > 1454931222502621
        rcases Nat.lt_or_ge 1467322723128883 n with h8 | h8
        · -- n > 1467322723128883
          rcases Nat.lt_or_ge 1471477148963357 n with h10 | h10
          · -- n > 1471477148963357
            rcases Nat.lt_or_ge 1475641825704433 n with h12 | h12
            · -- n > 1475641825704433
              exact RamareSaouter2003.prime_interval_nat_ladder_c04737 n (by omega) (by omega)
            · -- n <= 1475641825704433
              exact RamareSaouter2003.prime_interval_nat_ladder_c04736 n (by omega) (by omega)
          · -- n <= 1471477148963357
            exact RamareSaouter2003.prime_interval_nat_ladder_c04735 n (by omega) (by omega)
        · -- n <= 1467322723128883
          rcases Nat.lt_or_ge 1459049978142677 n with h10 | h10
          · -- n > 1459049978142677
            rcases Nat.lt_or_ge 1463180596748341 n with h12 | h12
            · -- n > 1463180596748341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04734 n (by omega) (by omega)
            · -- n <= 1463180596748341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04733 n (by omega) (by omega)
          · -- n <= 1459049978142677
            exact RamareSaouter2003.prime_interval_nat_ladder_c04732 n (by omega) (by omega)
      · -- n <= 1454931222502621
        rcases Nat.lt_or_ge 1442648940110401 n with h8 | h8
        · -- n > 1442648940110401
          rcases Nat.lt_or_ge 1446732482069311 n with h10 | h10
          · -- n > 1446732482069311
            rcases Nat.lt_or_ge 1450828349142691 n with h12 | h12
            · -- n > 1450828349142691
              exact RamareSaouter2003.prime_interval_nat_ladder_c04731 n (by omega) (by omega)
            · -- n <= 1450828349142691
              exact RamareSaouter2003.prime_interval_nat_ladder_c04730 n (by omega) (by omega)
          · -- n <= 1446732482069311
            exact RamareSaouter2003.prime_interval_nat_ladder_c04729 n (by omega) (by omega)
        · -- n <= 1442648940110401
          rcases Nat.lt_or_ge 1434516666040037 n with h10 | h10
          · -- n > 1434516666040037
            rcases Nat.lt_or_ge 1438577538194971 n with h12 | h12
            · -- n > 1438577538194971
              exact RamareSaouter2003.prime_interval_nat_ladder_c04728 n (by omega) (by omega)
            · -- n <= 1438577538194971
              exact RamareSaouter2003.prime_interval_nat_ladder_c04727 n (by omega) (by omega)
          · -- n <= 1434516666040037
            exact RamareSaouter2003.prime_interval_nat_ladder_c04726 n (by omega) (by omega)
  · -- n <= 1430466675481579
    rcases Nat.lt_or_ge 1378860271718467 n with h4 | h4
    · -- n > 1378860271718467
      rcases Nat.lt_or_ge 1402439344758953 n with h6 | h6
      · -- n > 1402439344758953
        rcases Nat.lt_or_ge 1414384587767051 n with h8 | h8
        · -- n > 1414384587767051
          rcases Nat.lt_or_ge 1422403479354581 n with h10 | h10
          · -- n > 1422403479354581
            rcases Nat.lt_or_ge 1426430040535673 n with h12 | h12
            · -- n > 1426430040535673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04725 n (by omega) (by omega)
            · -- n <= 1426430040535673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04724 n (by omega) (by omega)
          · -- n <= 1422403479354581
            rcases Nat.lt_or_ge 1418388639637759 n with h12 | h12
            · -- n > 1418388639637759
              exact RamareSaouter2003.prime_interval_nat_ladder_c04723 n (by omega) (by omega)
            · -- n <= 1418388639637759
              exact RamareSaouter2003.prime_interval_nat_ladder_c04722 n (by omega) (by omega)
        · -- n <= 1414384587767051
          rcases Nat.lt_or_ge 1406409888906577 n with h10 | h10
          · -- n > 1406409888906577
            rcases Nat.lt_or_ge 1410391829661313 n with h12 | h12
            · -- n > 1410391829661313
              exact RamareSaouter2003.prime_interval_nat_ladder_c04721 n (by omega) (by omega)
            · -- n <= 1410391829661313
              exact RamareSaouter2003.prime_interval_nat_ladder_c04720 n (by omega) (by omega)
          · -- n <= 1406409888906577
            exact RamareSaouter2003.prime_interval_nat_ladder_c04719 n (by omega) (by omega)
      · -- n <= 1402439344758953
        rcases Nat.lt_or_ge 1390598605356661 n with h8 | h8
        · -- n > 1390598605356661
          rcases Nat.lt_or_ge 1394535709738937 n with h10 | h10
          · -- n > 1394535709738937
            rcases Nat.lt_or_ge 1398482864674949 n with h12 | h12
            · -- n > 1398482864674949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04718 n (by omega) (by omega)
            · -- n <= 1398482864674949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04717 n (by omega) (by omega)
          · -- n <= 1394535709738937
            exact RamareSaouter2003.prime_interval_nat_ladder_c04716 n (by omega) (by omega)
        · -- n <= 1390598605356661
          rcases Nat.lt_or_ge 1382763555068317 n with h10 | h10
          · -- n > 1382763555068317
            rcases Nat.lt_or_ge 1386675258815141 n with h12 | h12
            · -- n > 1386675258815141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04715 n (by omega) (by omega)
            · -- n <= 1386675258815141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04714 n (by omega) (by omega)
          · -- n <= 1382763555068317
            exact RamareSaouter2003.prime_interval_nat_ladder_c04713 n (by omega) (by omega)
    · -- n <= 1378860271718467
      rcases Nat.lt_or_ge 1355670489342349 n with h6 | h6
      · -- n > 1355670489342349
        rcases Nat.lt_or_ge 1367215025426741 n with h8 | h8
        · -- n > 1367215025426741
          rcases Nat.lt_or_ge 1371085437664651 n with h10 | h10
          · -- n > 1371085437664651
            rcases Nat.lt_or_ge 1374967400946047 n with h12 | h12
            · -- n > 1374967400946047
              exact RamareSaouter2003.prime_interval_nat_ladder_c04712 n (by omega) (by omega)
            · -- n <= 1374967400946047
              exact RamareSaouter2003.prime_interval_nat_ladder_c04711 n (by omega) (by omega)
          · -- n <= 1371085437664651
            exact RamareSaouter2003.prime_interval_nat_ladder_c04710 n (by omega) (by omega)
        · -- n <= 1367215025426741
          rcases Nat.lt_or_ge 1359508756750273 n with h10 | h10
          · -- n > 1359508756750273
            rcases Nat.lt_or_ge 1363356435001823 n with h12 | h12
            · -- n > 1363356435001823
              exact RamareSaouter2003.prime_interval_nat_ladder_c04709 n (by omega) (by omega)
            · -- n <= 1363356435001823
              exact RamareSaouter2003.prime_interval_nat_ladder_c04708 n (by omega) (by omega)
          · -- n <= 1359508756750273
            exact RamareSaouter2003.prime_interval_nat_ladder_c04707 n (by omega) (by omega)
      · -- n <= 1355670489342349
        rcases Nat.lt_or_ge 1344221684057267 n with h8 | h8
        · -- n > 1344221684057267
          rcases Nat.lt_or_ge 1348027345619263 n with h10 | h10
          · -- n > 1348027345619263
            rcases Nat.lt_or_ge 1351843828076767 n with h12 | h12
            · -- n > 1351843828076767
              exact RamareSaouter2003.prime_interval_nat_ladder_c04706 n (by omega) (by omega)
            · -- n <= 1351843828076767
              exact RamareSaouter2003.prime_interval_nat_ladder_c04705 n (by omega) (by omega)
          · -- n <= 1348027345619263
            exact RamareSaouter2003.prime_interval_nat_ladder_c04704 n (by omega) (by omega)
        · -- n <= 1344221684057267
          rcases Nat.lt_or_ge 1336642295243923 n with h10 | h10
          · -- n > 1336642295243923
            rcases Nat.lt_or_ge 1340426528863529 n with h12 | h12
            · -- n > 1340426528863529
              exact RamareSaouter2003.prime_interval_nat_ladder_c04703 n (by omega) (by omega)
            · -- n <= 1340426528863529
              exact RamareSaouter2003.prime_interval_nat_ladder_c04702 n (by omega) (by omega)
          · -- n <= 1336642295243923
            exact RamareSaouter2003.prime_interval_nat_ladder_c04701 n (by omega) (by omega)
