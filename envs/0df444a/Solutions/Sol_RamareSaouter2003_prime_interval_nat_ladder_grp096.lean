-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T12:46:20.705419+00:00
-- url     : https://prove2.me/submissions/5086d353-2a1c-46ef-9123-43d3669a3c5c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04800

theorem solution (n : Nat)
    (hn : 1535198451695543 < n) (hupper : n <= 1768250287586501) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1647609505617323 n with h2 | h2
  · -- n > 1647609505617323
    rcases Nat.lt_or_ge 1704454389403291 n with h4 | h4
    · -- n > 1704454389403291
      rcases Nat.lt_or_ge 1733609896772371 n with h6 | h6
      · -- n > 1733609896772371
        rcases Nat.lt_or_ge 1748369223502711 n with h8 | h8
        · -- n > 1748369223502711
          rcases Nat.lt_or_ge 1758282330231937 n with h10 | h10
          · -- n > 1758282330231937
            rcases Nat.lt_or_ge 1763259806130947 n with h12 | h12
            · -- n > 1763259806130947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04800 n (by omega) (by omega)
            · -- n <= 1763259806130947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04799 n (by omega) (by omega)
          · -- n <= 1758282330231937
            rcases Nat.lt_or_ge 1753318839907711 n with h12 | h12
            · -- n > 1753318839907711
              exact RamareSaouter2003.prime_interval_nat_ladder_c04798 n (by omega) (by omega)
            · -- n <= 1753318839907711
              exact RamareSaouter2003.prime_interval_nat_ladder_c04797 n (by omega) (by omega)
        · -- n <= 1748369223502711
          rcases Nat.lt_or_ge 1738511737524791 n with h10 | h10
          · -- n > 1738511737524791
            rcases Nat.lt_or_ge 1743433199591819 n with h12 | h12
            · -- n > 1743433199591819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04796 n (by omega) (by omega)
            · -- n <= 1743433199591819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04795 n (by omega) (by omega)
          · -- n <= 1738511737524791
            exact RamareSaouter2003.prime_interval_nat_ladder_c04794 n (by omega) (by omega)
      · -- n <= 1733609896772371
        rcases Nat.lt_or_ge 1718968689924907 n with h8 | h8
        · -- n > 1718968689924907
          rcases Nat.lt_or_ge 1723835524320781 n with h10 | h10
          · -- n > 1723835524320781
            rcases Nat.lt_or_ge 1728715390114613 n with h12 | h12
            · -- n > 1728715390114613
              exact RamareSaouter2003.prime_interval_nat_ladder_c04793 n (by omega) (by omega)
            · -- n <= 1728715390114613
              exact RamareSaouter2003.prime_interval_nat_ladder_c04792 n (by omega) (by omega)
          · -- n <= 1723835524320781
            exact RamareSaouter2003.prime_interval_nat_ladder_c04791 n (by omega) (by omega)
        · -- n <= 1718968689924907
          rcases Nat.lt_or_ge 1709276251674851 n with h10 | h10
          · -- n > 1709276251674851
            rcases Nat.lt_or_ge 1714115527635403 n with h12 | h12
            · -- n > 1714115527635403
              exact RamareSaouter2003.prime_interval_nat_ladder_c04790 n (by omega) (by omega)
            · -- n <= 1714115527635403
              exact RamareSaouter2003.prime_interval_nat_ladder_c04789 n (by omega) (by omega)
          · -- n <= 1709276251674851
            exact RamareSaouter2003.prime_interval_nat_ladder_c04788 n (by omega) (by omega)
    · -- n <= 1704454389403291
      rcases Nat.lt_or_ge 1675791414277163 n with h6 | h6
      · -- n > 1675791414277163
        rcases Nat.lt_or_ge 1690061399144863 n with h8 | h8
        · -- n > 1690061399144863
          rcases Nat.lt_or_ge 1694845585026067 n with h10 | h10
          · -- n > 1694845585026067
            rcases Nat.lt_or_ge 1699643788636301 n with h12 | h12
            · -- n > 1699643788636301
              exact RamareSaouter2003.prime_interval_nat_ladder_c04787 n (by omega) (by omega)
            · -- n <= 1699643788636301
              exact RamareSaouter2003.prime_interval_nat_ladder_c04786 n (by omega) (by omega)
          · -- n <= 1694845585026067
            exact RamareSaouter2003.prime_interval_nat_ladder_c04785 n (by omega) (by omega)
        · -- n <= 1690061399144863
          rcases Nat.lt_or_ge 1680533809314859 n with h10 | h10
          · -- n > 1680533809314859
            rcases Nat.lt_or_ge 1685290870968799 n with h12 | h12
            · -- n > 1685290870968799
              exact RamareSaouter2003.prime_interval_nat_ladder_c04784 n (by omega) (by omega)
            · -- n <= 1685290870968799
              exact RamareSaouter2003.prime_interval_nat_ladder_c04783 n (by omega) (by omega)
          · -- n <= 1680533809314859
            exact RamareSaouter2003.prime_interval_nat_ladder_c04782 n (by omega) (by omega)
      · -- n <= 1675791414277163
        rcases Nat.lt_or_ge 1661640216385547 n with h8 | h8
        · -- n > 1661640216385547
          rcases Nat.lt_or_ge 1666344273430339 n with h10 | h10
          · -- n > 1666344273430339
            rcases Nat.lt_or_ge 1671061031345287 n with h12 | h12
            · -- n > 1671061031345287
              exact RamareSaouter2003.prime_interval_nat_ladder_c04781 n (by omega) (by omega)
            · -- n <= 1671061031345287
              exact RamareSaouter2003.prime_interval_nat_ladder_c04780 n (by omega) (by omega)
          · -- n <= 1666344273430339
            exact RamareSaouter2003.prime_interval_nat_ladder_c04779 n (by omega) (by omega)
        · -- n <= 1661640216385547
          rcases Nat.lt_or_ge 1652272619553461 n with h10 | h10
          · -- n > 1652272619553461
            rcases Nat.lt_or_ge 1656949975419719 n with h12 | h12
            · -- n > 1656949975419719
              exact RamareSaouter2003.prime_interval_nat_ladder_c04778 n (by omega) (by omega)
            · -- n <= 1656949975419719
              exact RamareSaouter2003.prime_interval_nat_ladder_c04777 n (by omega) (by omega)
          · -- n <= 1652272619553461
            exact RamareSaouter2003.prime_interval_nat_ladder_c04776 n (by omega) (by omega)
  · -- n <= 1647609505617323
    rcases Nat.lt_or_ge 1588164011556149 n with h4 | h4
    · -- n > 1588164011556149
      rcases Nat.lt_or_ge 1615331068006441 n with h6 | h6
      · -- n > 1615331068006441
        rcases Nat.lt_or_ge 1629084299475491 n with h8 | h8
        · -- n > 1629084299475491
          rcases Nat.lt_or_ge 1638320454300347 n with h10 | h10
          · -- n > 1638320454300347
            rcases Nat.lt_or_ge 1642958901634769 n with h12 | h12
            · -- n > 1642958901634769
              exact RamareSaouter2003.prime_interval_nat_ladder_c04775 n (by omega) (by omega)
            · -- n <= 1642958901634769
              exact RamareSaouter2003.prime_interval_nat_ladder_c04774 n (by omega) (by omega)
          · -- n <= 1638320454300347
            rcases Nat.lt_or_ge 1633695918027379 n with h12 | h12
            · -- n > 1633695918027379
              exact RamareSaouter2003.prime_interval_nat_ladder_c04773 n (by omega) (by omega)
            · -- n <= 1633695918027379
              exact RamareSaouter2003.prime_interval_nat_ladder_c04772 n (by omega) (by omega)
        · -- n <= 1629084299475491
          rcases Nat.lt_or_ge 1619900412571853 n with h10 | h10
          · -- n > 1619900412571853
            rcases Nat.lt_or_ge 1624484918855509 n with h12 | h12
            · -- n > 1624484918855509
              exact RamareSaouter2003.prime_interval_nat_ladder_c04771 n (by omega) (by omega)
            · -- n <= 1624484918855509
              exact RamareSaouter2003.prime_interval_nat_ladder_c04770 n (by omega) (by omega)
          · -- n <= 1619900412571853
            exact RamareSaouter2003.prime_interval_nat_ladder_c04769 n (by omega) (by omega)
      · -- n <= 1615331068006441
        rcases Nat.lt_or_ge 1601690325032323 n with h8 | h8
        · -- n > 1601690325032323
          rcases Nat.lt_or_ge 1606224240559577 n with h10 | h10
          · -- n > 1606224240559577
            rcases Nat.lt_or_ge 1610771464815397 n with h12 | h12
            · -- n > 1610771464815397
              exact RamareSaouter2003.prime_interval_nat_ladder_c04768 n (by omega) (by omega)
            · -- n <= 1610771464815397
              exact RamareSaouter2003.prime_interval_nat_ladder_c04767 n (by omega) (by omega)
          · -- n <= 1606224240559577
            exact RamareSaouter2003.prime_interval_nat_ladder_c04766 n (by omega) (by omega)
        · -- n <= 1601690325032323
          rcases Nat.lt_or_ge 1592660557046423 n with h10 | h10
          · -- n > 1592660557046423
            rcases Nat.lt_or_ge 1597168973153797 n with h12 | h12
            · -- n > 1597168973153797
              exact RamareSaouter2003.prime_interval_nat_ladder_c04765 n (by omega) (by omega)
            · -- n <= 1597168973153797
              exact RamareSaouter2003.prime_interval_nat_ladder_c04764 n (by omega) (by omega)
          · -- n <= 1592660557046423
            exact RamareSaouter2003.prime_interval_nat_ladder_c04763 n (by omega) (by omega)
    · -- n <= 1588164011556149
      rcases Nat.lt_or_ge 1561455341648869 n with h6 | h6
      · -- n > 1561455341648869
        rcases Nat.lt_or_ge 1574752752707921 n with h8 | h8
        · -- n > 1574752752707921
          rcases Nat.lt_or_ge 1579210097509103 n with h10 | h10
          · -- n > 1579210097509103
            rcases Nat.lt_or_ge 1583680986230789 n with h12 | h12
            · -- n > 1583680986230789
              exact RamareSaouter2003.prime_interval_nat_ladder_c04762 n (by omega) (by omega)
            · -- n <= 1583680986230789
              exact RamareSaouter2003.prime_interval_nat_ladder_c04761 n (by omega) (by omega)
          · -- n <= 1579210097509103
            exact RamareSaouter2003.prime_interval_nat_ladder_c04760 n (by omega) (by omega)
        · -- n <= 1574752752707921
          rcases Nat.lt_or_ge 1565875953125999 n with h10 | h10
          · -- n > 1565875953125999
            rcases Nat.lt_or_ge 1570309396066681 n with h12 | h12
            · -- n > 1570309396066681
              exact RamareSaouter2003.prime_interval_nat_ladder_c04759 n (by omega) (by omega)
            · -- n <= 1570309396066681
              exact RamareSaouter2003.prime_interval_nat_ladder_c04758 n (by omega) (by omega)
          · -- n <= 1565875953125999
            exact RamareSaouter2003.prime_interval_nat_ladder_c04757 n (by omega) (by omega)
      · -- n <= 1561455341648869
        rcases Nat.lt_or_ge 1548272938134539 n with h8 | h8
        · -- n > 1548272938134539
          rcases Nat.lt_or_ge 1552654297330691 n with h10 | h10
          · -- n > 1552654297330691
            rcases Nat.lt_or_ge 1557047289942821 n with h12 | h12
            · -- n > 1557047289942821
              exact RamareSaouter2003.prime_interval_nat_ladder_c04756 n (by omega) (by omega)
            · -- n <= 1557047289942821
              exact RamareSaouter2003.prime_interval_nat_ladder_c04755 n (by omega) (by omega)
          · -- n <= 1552654297330691
            exact RamareSaouter2003.prime_interval_nat_ladder_c04754 n (by omega) (by omega)
        · -- n <= 1548272938134539
          rcases Nat.lt_or_ge 1539544569668011 n with h10 | h10
          · -- n > 1539544569668011
            rcases Nat.lt_or_ge 1543903193900653 n with h12 | h12
            · -- n > 1543903193900653
              exact RamareSaouter2003.prime_interval_nat_ladder_c04753 n (by omega) (by omega)
            · -- n <= 1543903193900653
              exact RamareSaouter2003.prime_interval_nat_ladder_c04752 n (by omega) (by omega)
          · -- n <= 1539544569668011
            exact RamareSaouter2003.prime_interval_nat_ladder_c04751 n (by omega) (by omega)
