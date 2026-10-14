-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T13:03:38.98238+00:00
-- url     : https://prove2.me/submissions/a2007cbf-5a53-42da-8c48-2ef815a23fba

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04850

theorem solution (n : Nat)
    (hn : 1768250287586501 < n) (hupper : n <= 2036672748741173) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1897725041145617 n with h2 | h2
  · -- n > 1897725041145617
    rcases Nat.lt_or_ge 1963193984825839 n with h4 | h4
    · -- n > 1963193984825839
      rcases Nat.lt_or_ge 1996770486259763 n with h6 | h6
      · -- n > 1996770486259763
        rcases Nat.lt_or_ge 2013775486978679 n with h8 | h8
        · -- n > 2013775486978679
          rcases Nat.lt_or_ge 2025191691891869 n with h10 | h10
          · -- n > 2025191691891869
            rcases Nat.lt_or_ge 2030925416379329 n with h12 | h12
            · -- n > 2030925416379329
              exact RamareSaouter2003.prime_interval_nat_ladder_c04850 n (by omega) (by omega)
            · -- n <= 2030925416379329
              exact RamareSaouter2003.prime_interval_nat_ladder_c04849 n (by omega) (by omega)
          · -- n <= 2025191691891869
            rcases Nat.lt_or_ge 2019475510722409 n with h12 | h12
            · -- n > 2019475510722409
              exact RamareSaouter2003.prime_interval_nat_ladder_c04848 n (by omega) (by omega)
            · -- n <= 2019475510722409
              exact RamareSaouter2003.prime_interval_nat_ladder_c04847 n (by omega) (by omega)
        · -- n <= 2013775486978679
          rcases Nat.lt_or_ge 2002423769061979 n with h10 | h10
          · -- n > 2002423769061979
            rcases Nat.lt_or_ge 2008091314417247 n with h12 | h12
            · -- n > 2008091314417247
              exact RamareSaouter2003.prime_interval_nat_ladder_c04846 n (by omega) (by omega)
            · -- n <= 2008091314417247
              exact RamareSaouter2003.prime_interval_nat_ladder_c04845 n (by omega) (by omega)
          · -- n <= 2002423769061979
            exact RamareSaouter2003.prime_interval_nat_ladder_c04844 n (by omega) (by omega)
      · -- n <= 1996770486259763
        rcases Nat.lt_or_ge 1979911630160923 n with h8 | h8
        · -- n > 1979911630160923
          rcases Nat.lt_or_ge 1985512850001539 n with h10 | h10
          · -- n > 1985512850001539
            rcases Nat.lt_or_ge 1991133139711801 n with h12 | h12
            · -- n > 1991133139711801
              exact RamareSaouter2003.prime_interval_nat_ladder_c04843 n (by omega) (by omega)
            · -- n <= 1991133139711801
              exact RamareSaouter2003.prime_interval_nat_ladder_c04842 n (by omega) (by omega)
          · -- n <= 1985512850001539
            exact RamareSaouter2003.prime_interval_nat_ladder_c04841 n (by omega) (by omega)
        · -- n <= 1979911630160923
          rcases Nat.lt_or_ge 1968749337790643 n with h10 | h10
          · -- n > 1968749337790643
            rcases Nat.lt_or_ge 1974321875015507 n with h12 | h12
            · -- n > 1974321875015507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04840 n (by omega) (by omega)
            · -- n <= 1974321875015507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04839 n (by omega) (by omega)
          · -- n <= 1968749337790643
            exact RamareSaouter2003.prime_interval_nat_ladder_c04838 n (by omega) (by omega)
    · -- n <= 1963193984825839
      rcases Nat.lt_or_ge 1930179573114229 n with h6 | h6
      · -- n > 1930179573114229
        rcases Nat.lt_or_ge 1946617457941987 n with h8 | h8
        · -- n > 1946617457941987
          rcases Nat.lt_or_ge 1952128560828079 n with h10 | h10
          · -- n > 1952128560828079
            rcases Nat.lt_or_ge 1957651611491347 n with h12 | h12
            · -- n > 1957651611491347
              exact RamareSaouter2003.prime_interval_nat_ladder_c04837 n (by omega) (by omega)
            · -- n <= 1957651611491347
              exact RamareSaouter2003.prime_interval_nat_ladder_c04836 n (by omega) (by omega)
          · -- n <= 1952128560828079
            exact RamareSaouter2003.prime_interval_nat_ladder_c04835 n (by omega) (by omega)
        · -- n <= 1946617457941987
          rcases Nat.lt_or_ge 1935643790778547 n with h10 | h10
          · -- n > 1935643790778547
            rcases Nat.lt_or_ge 1941123487588777 n with h12 | h12
            · -- n > 1941123487588777
              exact RamareSaouter2003.prime_interval_nat_ladder_c04834 n (by omega) (by omega)
            · -- n <= 1941123487588777
              exact RamareSaouter2003.prime_interval_nat_ladder_c04833 n (by omega) (by omega)
          · -- n <= 1935643790778547
            exact RamareSaouter2003.prime_interval_nat_ladder_c04832 n (by omega) (by omega)
      · -- n <= 1930179573114229
        rcases Nat.lt_or_ge 1913880593767847 n with h8 | h8
        · -- n > 1913880593767847
          rcases Nat.lt_or_ge 1919298401015857 n with h10 | h10
          · -- n > 1919298401015857
            rcases Nat.lt_or_ge 1924730624094827 n with h12 | h12
            · -- n > 1924730624094827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04831 n (by omega) (by omega)
            · -- n <= 1924730624094827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04830 n (by omega) (by omega)
          · -- n <= 1919298401015857
            exact RamareSaouter2003.prime_interval_nat_ladder_c04829 n (by omega) (by omega)
        · -- n <= 1913880593767847
          rcases Nat.lt_or_ge 1903095171058009 n with h10 | h10
          · -- n > 1903095171058009
            rcases Nat.lt_or_ge 1908479441496977 n with h12 | h12
            · -- n > 1908479441496977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04828 n (by omega) (by omega)
            · -- n <= 1908479441496977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04827 n (by omega) (by omega)
          · -- n <= 1903095171058009
            exact RamareSaouter2003.prime_interval_nat_ladder_c04826 n (by omega) (by omega)
  · -- n <= 1897725041145617
    rcases Nat.lt_or_ge 1829257856578409 n with h4 | h4
    · -- n > 1829257856578409
      rcases Nat.lt_or_ge 1860543772318753 n with h6 | h6
      · -- n > 1860543772318753
        rcases Nat.lt_or_ge 1876387444428463 n with h8 | h8
        · -- n > 1876387444428463
          rcases Nat.lt_or_ge 1887027350747743 n with h10 | h10
          · -- n > 1887027350747743
            rcases Nat.lt_or_ge 1892368326627601 n with h12 | h12
            · -- n > 1892368326627601
              exact RamareSaouter2003.prime_interval_nat_ladder_c04825 n (by omega) (by omega)
            · -- n <= 1892368326627601
              exact RamareSaouter2003.prime_interval_nat_ladder_c04824 n (by omega) (by omega)
          · -- n <= 1887027350747743
            rcases Nat.lt_or_ge 1881699734718161 n with h12 | h12
            · -- n > 1881699734718161
              exact RamareSaouter2003.prime_interval_nat_ladder_c04823 n (by omega) (by omega)
            · -- n <= 1881699734718161
              exact RamareSaouter2003.prime_interval_nat_ladder_c04822 n (by omega) (by omega)
        · -- n <= 1876387444428463
          rcases Nat.lt_or_ge 1865810624184011 n with h10 | h10
          · -- n > 1865810624184011
            rcases Nat.lt_or_ge 1871093047800377 n with h12 | h12
            · -- n > 1871093047800377
              exact RamareSaouter2003.prime_interval_nat_ladder_c04821 n (by omega) (by omega)
            · -- n <= 1871093047800377
              exact RamareSaouter2003.prime_interval_nat_ladder_c04820 n (by omega) (by omega)
          · -- n <= 1865810624184011
            exact RamareSaouter2003.prime_interval_nat_ladder_c04819 n (by omega) (by omega)
      · -- n <= 1860543772318753
        rcases Nat.lt_or_ge 1844835567471269 n with h8 | h8
        · -- n > 1844835567471269
          rcases Nat.lt_or_ge 1850056154174251 n with h10 | h10
          · -- n > 1850056154174251
            rcases Nat.lt_or_ge 1855291521914179 n with h12 | h12
            · -- n > 1855291521914179
              exact RamareSaouter2003.prime_interval_nat_ladder_c04818 n (by omega) (by omega)
            · -- n <= 1855291521914179
              exact RamareSaouter2003.prime_interval_nat_ladder_c04817 n (by omega) (by omega)
          · -- n <= 1850056154174251
            exact RamareSaouter2003.prime_interval_nat_ladder_c04816 n (by omega) (by omega)
        · -- n <= 1844835567471269
          rcases Nat.lt_or_ge 1834436579637107 n with h10 | h10
          · -- n > 1834436579637107
            rcases Nat.lt_or_ge 1839629743137619 n with h12 | h12
            · -- n > 1839629743137619
              exact RamareSaouter2003.prime_interval_nat_ladder_c04815 n (by omega) (by omega)
            · -- n <= 1839629743137619
              exact RamareSaouter2003.prime_interval_nat_ladder_c04814 n (by omega) (by omega)
          · -- n <= 1834436579637107
            exact RamareSaouter2003.prime_interval_nat_ladder_c04813 n (by omega) (by omega)
    · -- n <= 1829257856578409
      rcases Nat.lt_or_ge 1798496494670459 n with h6 | h6
      · -- n > 1798496494670459
        rcases Nat.lt_or_ge 1813814503154443 n with h8 | h8
        · -- n > 1813814503154443
          rcases Nat.lt_or_ge 1818948388522571 n with h10 | h10
          · -- n > 1818948388522571
            rcases Nat.lt_or_ge 1824094223495743 n with h12 | h12
            · -- n > 1824094223495743
              exact RamareSaouter2003.prime_interval_nat_ladder_c04812 n (by omega) (by omega)
            · -- n <= 1824094223495743
              exact RamareSaouter2003.prime_interval_nat_ladder_c04811 n (by omega) (by omega)
          · -- n <= 1818948388522571
            exact RamareSaouter2003.prime_interval_nat_ladder_c04810 n (by omega) (by omega)
        · -- n <= 1813814503154443
          rcases Nat.lt_or_ge 1803588202717307 n with h10 | h10
          · -- n > 1803588202717307
            rcases Nat.lt_or_ge 1808693571041893 n with h12 | h12
            · -- n > 1808693571041893
              exact RamareSaouter2003.prime_interval_nat_ladder_c04809 n (by omega) (by omega)
            · -- n <= 1808693571041893
              exact RamareSaouter2003.prime_interval_nat_ladder_c04808 n (by omega) (by omega)
          · -- n <= 1803588202717307
            exact RamareSaouter2003.prime_interval_nat_ladder_c04807 n (by omega) (by omega)
      · -- n <= 1798496494670459
        rcases Nat.lt_or_ge 1783306869011153 n with h8 | h8
        · -- n > 1783306869011153
          rcases Nat.lt_or_ge 1788355647698909 n with h10 | h10
          · -- n > 1788355647698909
            rcases Nat.lt_or_ge 1793419015528073 n with h12 | h12
            · -- n > 1793419015528073
              exact RamareSaouter2003.prime_interval_nat_ladder_c04806 n (by omega) (by omega)
            · -- n <= 1793419015528073
              exact RamareSaouter2003.prime_interval_nat_ladder_c04805 n (by omega) (by omega)
          · -- n <= 1788355647698909
            exact RamareSaouter2003.prime_interval_nat_ladder_c04804 n (by omega) (by omega)
        · -- n <= 1783306869011153
          rcases Nat.lt_or_ge 1773254729559527 n with h10 | h10
          · -- n > 1773254729559527
            rcases Nat.lt_or_ge 1778274676801501 n with h12 | h12
            · -- n > 1778274676801501
              exact RamareSaouter2003.prime_interval_nat_ladder_c04803 n (by omega) (by omega)
            · -- n <= 1778274676801501
              exact RamareSaouter2003.prime_interval_nat_ladder_c04802 n (by omega) (by omega)
          · -- n <= 1773254729559527
            exact RamareSaouter2003.prime_interval_nat_ladder_c04801 n (by omega) (by omega)
