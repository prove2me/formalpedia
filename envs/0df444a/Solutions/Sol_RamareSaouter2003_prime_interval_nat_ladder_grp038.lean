-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T12:42:51.999987+00:00
-- url     : https://prove2.me/submissions/31463a40-8ac5-4b3d-9981-98ede462dd2c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01900

theorem solution (n : Nat)
    (hn : 857157375181 < n) (hupper : n <= 973153707433) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 913299015833 n with h2 | h2
  · -- n > 913299015833
    rcases Nat.lt_or_ge 941550992647 n with h4 | h4
    · -- n > 941550992647
      rcases Nat.lt_or_ge 956006089711 n with h6 | h6
      · -- n > 956006089711
        rcases Nat.lt_or_ge 963317415173 n with h8 | h8
        · -- n > 963317415173
          rcases Nat.lt_or_ge 968222955937 n with h10 | h10
          · -- n > 968222955937
            rcases Nat.lt_or_ge 970685172217 n with h12 | h12
            · -- n > 970685172217
              exact RamareSaouter2003.prime_interval_nat_ladder_c01900 n (by omega) (by omega)
            · -- n <= 970685172217
              exact RamareSaouter2003.prime_interval_nat_ladder_c01899 n (by omega) (by omega)
          · -- n <= 968222955937
            rcases Nat.lt_or_ge 965767042411 n with h12 | h12
            · -- n > 965767042411
              exact RamareSaouter2003.prime_interval_nat_ladder_c01898 n (by omega) (by omega)
            · -- n <= 965767042411
              exact RamareSaouter2003.prime_interval_nat_ladder_c01897 n (by omega) (by omega)
        · -- n <= 963317415173
          rcases Nat.lt_or_ge 958436955043 n with h10 | h10
          · -- n > 958436955043
            rcases Nat.lt_or_ge 960874058161 n with h12 | h12
            · -- n > 960874058161
              exact RamareSaouter2003.prime_interval_nat_ladder_c01896 n (by omega) (by omega)
            · -- n <= 960874058161
              exact RamareSaouter2003.prime_interval_nat_ladder_c01895 n (by omega) (by omega)
          · -- n <= 958436955043
            exact RamareSaouter2003.prime_interval_nat_ladder_c01894 n (by omega) (by omega)
      · -- n <= 956006089711
        rcases Nat.lt_or_ge 948750759839 n with h8 | h8
        · -- n > 948750759839
          rcases Nat.lt_or_ge 951163008109 n with h10 | h10
          · -- n > 951163008109
            rcases Nat.lt_or_ge 953581446127 n with h12 | h12
            · -- n > 953581446127
              exact RamareSaouter2003.prime_interval_nat_ladder_c01893 n (by omega) (by omega)
            · -- n <= 953581446127
              exact RamareSaouter2003.prime_interval_nat_ladder_c01892 n (by omega) (by omega)
          · -- n <= 951163008109
            exact RamareSaouter2003.prime_interval_nat_ladder_c01891 n (by omega) (by omega)
        · -- n <= 948750759839
          rcases Nat.lt_or_ge 943944767999 n with h10 | h10
          · -- n > 943944767999
            rcases Nat.lt_or_ge 946344685043 n with h12 | h12
            · -- n > 946344685043
              exact RamareSaouter2003.prime_interval_nat_ladder_c01890 n (by omega) (by omega)
            · -- n <= 946344685043
              exact RamareSaouter2003.prime_interval_nat_ladder_c01889 n (by omega) (by omega)
          · -- n <= 943944767999
            exact RamareSaouter2003.prime_interval_nat_ladder_c01888 n (by omega) (by omega)
    · -- n <= 941550992647
      rcases Nat.lt_or_ge 927316432927 n with h6 | h6
      · -- n > 927316432927
        rcases Nat.lt_or_ge 934406359111 n with h8 | h8
        · -- n > 934406359111
          rcases Nat.lt_or_ge 936781804081 n with h10 | h10
          · -- n > 936781804081
            rcases Nat.lt_or_ge 939163343281 n with h12 | h12
            · -- n > 939163343281
              exact RamareSaouter2003.prime_interval_nat_ladder_c01887 n (by omega) (by omega)
            · -- n <= 939163343281
              exact RamareSaouter2003.prime_interval_nat_ladder_c01886 n (by omega) (by omega)
          · -- n <= 936781804081
            exact RamareSaouter2003.prime_interval_nat_ladder_c01885 n (by omega) (by omega)
        · -- n <= 934406359111
          rcases Nat.lt_or_ge 929673689177 n with h10 | h10
          · -- n > 929673689177
            rcases Nat.lt_or_ge 932036992709 n with h12 | h12
            · -- n > 932036992709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01884 n (by omega) (by omega)
            · -- n <= 932036992709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01883 n (by omega) (by omega)
          · -- n <= 929673689177
            exact RamareSaouter2003.prime_interval_nat_ladder_c01882 n (by omega) (by omega)
      · -- n <= 927316432927
        rcases Nat.lt_or_ge 920280791713 n with h8 | h8
        · -- n > 920280791713
          rcases Nat.lt_or_ge 922619999731 n with h10 | h10
          · -- n > 922619999731
            rcases Nat.lt_or_ge 924965208257 n with h12 | h12
            · -- n > 924965208257
              exact RamareSaouter2003.prime_interval_nat_ladder_c01881 n (by omega) (by omega)
            · -- n <= 924965208257
              exact RamareSaouter2003.prime_interval_nat_ladder_c01880 n (by omega) (by omega)
          · -- n <= 922619999731
            exact RamareSaouter2003.prime_interval_nat_ladder_c01879 n (by omega) (by omega)
        · -- n <= 920280791713
          rcases Nat.lt_or_ge 915620315171 n with h10 | h10
          · -- n > 915620315171
            rcases Nat.lt_or_ge 917947568647 n with h12 | h12
            · -- n > 917947568647
              exact RamareSaouter2003.prime_interval_nat_ladder_c01878 n (by omega) (by omega)
            · -- n <= 917947568647
              exact RamareSaouter2003.prime_interval_nat_ladder_c01877 n (by omega) (by omega)
          · -- n <= 915620315171
            exact RamareSaouter2003.prime_interval_nat_ladder_c01876 n (by omega) (by omega)
  · -- n <= 913299015833
    rcases Nat.lt_or_ge 883657015271 n with h4 | h4
    · -- n > 883657015271
      rcases Nat.lt_or_ge 897215351453 n with h6 | h6
      · -- n > 897215351453
        rcases Nat.lt_or_ge 904073053517 n with h8 | h8
        · -- n > 904073053517
          rcases Nat.lt_or_ge 908674218271 n with h10 | h10
          · -- n > 908674218271
            rcases Nat.lt_or_ge 910983655343 n with h12 | h12
            · -- n > 910983655343
              exact RamareSaouter2003.prime_interval_nat_ladder_c01875 n (by omega) (by omega)
            · -- n <= 910983655343
              exact RamareSaouter2003.prime_interval_nat_ladder_c01874 n (by omega) (by omega)
          · -- n <= 908674218271
            rcases Nat.lt_or_ge 906370689431 n with h12 | h12
            · -- n > 906370689431
              exact RamareSaouter2003.prime_interval_nat_ladder_c01873 n (by omega) (by omega)
            · -- n <= 906370689431
              exact RamareSaouter2003.prime_interval_nat_ladder_c01872 n (by omega) (by omega)
        · -- n <= 904073053517
          rcases Nat.lt_or_ge 899495399701 n with h10 | h10
          · -- n > 899495399701
            rcases Nat.lt_or_ge 901781295271 n with h12 | h12
            · -- n > 901781295271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01871 n (by omega) (by omega)
            · -- n <= 901781295271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01870 n (by omega) (by omega)
          · -- n <= 899495399701
            exact RamareSaouter2003.prime_interval_nat_ladder_c01869 n (by omega) (by omega)
      · -- n <= 897215351453
        rcases Nat.lt_or_ge 890410140469 n with h8 | h8
        · -- n > 890410140469
          rcases Nat.lt_or_ge 892672736899 n with h10 | h10
          · -- n > 892672736899
            rcases Nat.lt_or_ge 894941135533 n with h12 | h12
            · -- n > 894941135533
              exact RamareSaouter2003.prime_interval_nat_ladder_c01868 n (by omega) (by omega)
            · -- n <= 894941135533
              exact RamareSaouter2003.prime_interval_nat_ladder_c01867 n (by omega) (by omega)
          · -- n <= 892672736899
            exact RamareSaouter2003.prime_interval_nat_ladder_c01866 n (by omega) (by omega)
        · -- n <= 890410140469
          rcases Nat.lt_or_ge 885902294593 n with h10 | h10
          · -- n > 885902294593
            rcases Nat.lt_or_ge 888153331379 n with h12 | h12
            · -- n > 888153331379
              exact RamareSaouter2003.prime_interval_nat_ladder_c01865 n (by omega) (by omega)
            · -- n <= 888153331379
              exact RamareSaouter2003.prime_interval_nat_ladder_c01864 n (by omega) (by omega)
          · -- n <= 885902294593
            exact RamareSaouter2003.prime_interval_nat_ladder_c01863 n (by omega) (by omega)
    · -- n <= 883657015271
      rcases Nat.lt_or_ge 870305416633 n with h6 | h6
      · -- n > 870305416633
        rcases Nat.lt_or_ge 876955573639 n with h8 | h8
        · -- n > 876955573639
          rcases Nat.lt_or_ge 879183669601 n with h10 | h10
          · -- n > 879183669601
            rcases Nat.lt_or_ge 881417478583 n with h12 | h12
            · -- n > 881417478583
              exact RamareSaouter2003.prime_interval_nat_ladder_c01862 n (by omega) (by omega)
            · -- n <= 881417478583
              exact RamareSaouter2003.prime_interval_nat_ladder_c01861 n (by omega) (by omega)
          · -- n <= 879183669601
            exact RamareSaouter2003.prime_interval_nat_ladder_c01860 n (by omega) (by omega)
        · -- n <= 876955573639
          rcases Nat.lt_or_ge 872516461919 n with h10 | h10
          · -- n > 872516461919
            rcases Nat.lt_or_ge 874733176061 n with h12 | h12
            · -- n > 874733176061
              exact RamareSaouter2003.prime_interval_nat_ladder_c01859 n (by omega) (by omega)
            · -- n <= 874733176061
              exact RamareSaouter2003.prime_interval_nat_ladder_c01858 n (by omega) (by omega)
          · -- n <= 872516461919
            exact RamareSaouter2003.prime_interval_nat_ladder_c01857 n (by omega) (by omega)
      · -- n <= 870305416633
        rcases Nat.lt_or_ge 863706147929 n with h8 | h8
        · -- n > 863706147929
          rcases Nat.lt_or_ge 865900274177 n with h10 | h10
          · -- n > 865900274177
            rcases Nat.lt_or_ge 868100025571 n with h12 | h12
            · -- n > 868100025571
              exact RamareSaouter2003.prime_interval_nat_ladder_c01856 n (by omega) (by omega)
            · -- n <= 868100025571
              exact RamareSaouter2003.prime_interval_nat_ladder_c01855 n (by omega) (by omega)
          · -- n <= 865900274177
            exact RamareSaouter2003.prime_interval_nat_ladder_c01854 n (by omega) (by omega)
        · -- n <= 863706147929
          rcases Nat.lt_or_ge 859334712947 n with h10 | h10
          · -- n > 859334712947
            rcases Nat.lt_or_ge 861517632361 n with h12 | h12
            · -- n > 861517632361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01853 n (by omega) (by omega)
            · -- n <= 861517632361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01852 n (by omega) (by omega)
          · -- n <= 859334712947
            exact RamareSaouter2003.prime_interval_nat_ladder_c01851 n (by omega) (by omega)
