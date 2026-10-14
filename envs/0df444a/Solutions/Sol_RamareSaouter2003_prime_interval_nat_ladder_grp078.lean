-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T07:45:53.955993+00:00
-- url     : https://prove2.me/submissions/a2a55c42-4603-4ad7-b060-d0ae6dba3700

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03900

theorem solution (n : Nat)
    (hn : 124030886084041 < n) (hupper : n <= 140346528528637) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 131936743525891 n with h2 | h2
  · -- n > 131936743525891
    rcases Nat.lt_or_ge 135908618967881 n with h4 | h4
    · -- n > 135908618967881
      rcases Nat.lt_or_ge 137939173300969 n with h6 | h6
      · -- n > 137939173300969
        rcases Nat.lt_or_ge 138965798922593 n with h8 | h8
        · -- n > 138965798922593
          rcases Nat.lt_or_ge 139654457368703 n with h10 | h10
          · -- n > 139654457368703
            rcases Nat.lt_or_ge 140000065304461 n with h12 | h12
            · -- n > 140000065304461
              exact RamareSaouter2003.prime_interval_nat_ladder_c03900 n (by omega) (by omega)
            · -- n <= 140000065304461
              exact RamareSaouter2003.prime_interval_nat_ladder_c03899 n (by omega) (by omega)
          · -- n <= 139654457368703
            rcases Nat.lt_or_ge 139309702610167 n with h12 | h12
            · -- n > 139309702610167
              exact RamareSaouter2003.prime_interval_nat_ladder_c03898 n (by omega) (by omega)
            · -- n <= 139309702610167
              exact RamareSaouter2003.prime_interval_nat_ladder_c03897 n (by omega) (by omega)
        · -- n <= 138965798922593
          rcases Nat.lt_or_ge 138280536361103 n with h10 | h10
          · -- n > 138280536361103
            rcases Nat.lt_or_ge 138622744204801 n with h12 | h12
            · -- n > 138622744204801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03896 n (by omega) (by omega)
            · -- n <= 138622744204801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03895 n (by omega) (by omega)
          · -- n <= 138280536361103
            exact RamareSaouter2003.prime_interval_nat_ladder_c03894 n (by omega) (by omega)
      · -- n <= 137939173300969
        rcases Nat.lt_or_ge 136920131992877 n with h8 | h8
        · -- n > 136920131992877
          rcases Nat.lt_or_ge 137258973194729 n with h10 | h10
          · -- n > 137258973194729
            rcases Nat.lt_or_ge 137598652939091 n with h12 | h12
            · -- n > 137598652939091
              exact RamareSaouter2003.prime_interval_nat_ladder_c03893 n (by omega) (by omega)
            · -- n <= 137598652939091
              exact RamareSaouter2003.prime_interval_nat_ladder_c03892 n (by omega) (by omega)
          · -- n <= 137258973194729
            exact RamareSaouter2003.prime_interval_nat_ladder_c03891 n (by omega) (by omega)
        · -- n <= 136920131992877
          rcases Nat.lt_or_ge 136244956941887 n with h10 | h10
          · -- n > 136244956941887
            rcases Nat.lt_or_ge 136582127263613 n with h12 | h12
            · -- n > 136582127263613
              exact RamareSaouter2003.prime_interval_nat_ladder_c03890 n (by omega) (by omega)
            · -- n <= 136582127263613
              exact RamareSaouter2003.prime_interval_nat_ladder_c03889 n (by omega) (by omega)
          · -- n <= 136244956941887
            exact RamareSaouter2003.prime_interval_nat_ladder_c03888 n (by omega) (by omega)
    · -- n <= 135908618967881
      rcases Nat.lt_or_ge 133907955714859 n with h6 | h6
      · -- n > 133907955714859
        rcases Nat.lt_or_ge 134904578610377 n with h8 | h8
        · -- n > 134904578610377
          rcases Nat.lt_or_ge 135238431849233 n with h10 | h10
          · -- n > 135238431849233
            rcases Nat.lt_or_ge 135573111286849 n with h12 | h12
            · -- n > 135573111286849
              exact RamareSaouter2003.prime_interval_nat_ladder_c03887 n (by omega) (by omega)
            · -- n <= 135573111286849
              exact RamareSaouter2003.prime_interval_nat_ladder_c03886 n (by omega) (by omega)
          · -- n <= 135238431849233
            exact RamareSaouter2003.prime_interval_nat_ladder_c03885 n (by omega) (by omega)
        · -- n <= 134904578610377
          rcases Nat.lt_or_ge 134239342575139 n with h10 | h10
          · -- n > 134239342575139
            rcases Nat.lt_or_ge 134571549530497 n with h12 | h12
            · -- n > 134571549530497
              exact RamareSaouter2003.prime_interval_nat_ladder_c03884 n (by omega) (by omega)
            · -- n <= 134571549530497
              exact RamareSaouter2003.prime_interval_nat_ladder_c03883 n (by omega) (by omega)
          · -- n <= 134239342575139
            exact RamareSaouter2003.prime_interval_nat_ladder_c03882 n (by omega) (by omega)
      · -- n <= 133907955714859
        rcases Nat.lt_or_ge 132918695484229 n with h8 | h8
        · -- n > 132918695484229
          rcases Nat.lt_or_ge 133247634186461 n with h10 | h10
          · -- n > 133247634186461
            rcases Nat.lt_or_ge 133577386925119 n with h12 | h12
            · -- n > 133577386925119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03881 n (by omega) (by omega)
            · -- n <= 133577386925119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03880 n (by omega) (by omega)
          · -- n <= 133247634186461
            exact RamareSaouter2003.prime_interval_nat_ladder_c03879 n (by omega) (by omega)
        · -- n <= 132918695484229
          rcases Nat.lt_or_ge 132263252156039 n with h10 | h10
          · -- n > 132263252156039
            rcases Nat.lt_or_ge 132590568808967 n with h12 | h12
            · -- n > 132590568808967
              exact RamareSaouter2003.prime_interval_nat_ladder_c03878 n (by omega) (by omega)
            · -- n <= 132590568808967
              exact RamareSaouter2003.prime_interval_nat_ladder_c03877 n (by omega) (by omega)
          · -- n <= 132263252156039
            exact RamareSaouter2003.prime_interval_nat_ladder_c03876 n (by omega) (by omega)
  · -- n <= 131936743525891
    rcases Nat.lt_or_ge 127764760494247 n with h4 | h4
    · -- n > 127764760494247
      rcases Nat.lt_or_ge 129673640814269 n with h6 | h6
      · -- n > 129673640814269
        rcases Nat.lt_or_ge 130638749411993 n with h8 | h8
        · -- n > 130638749411993
          rcases Nat.lt_or_ge 131286142359859 n with h10 | h10
          · -- n > 131286142359859
            rcases Nat.lt_or_ge 131611040923757 n with h12 | h12
            · -- n > 131611040923757
              exact RamareSaouter2003.prime_interval_nat_ladder_c03875 n (by omega) (by omega)
            · -- n <= 131611040923757
              exact RamareSaouter2003.prime_interval_nat_ladder_c03874 n (by omega) (by omega)
          · -- n <= 131286142359859
            rcases Nat.lt_or_ge 130962045849241 n with h12 | h12
            · -- n > 130962045849241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03873 n (by omega) (by omega)
            · -- n <= 130962045849241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03872 n (by omega) (by omega)
        · -- n <= 130638749411993
          rcases Nat.lt_or_ge 129994548862271 n with h10 | h10
          · -- n > 129994548862271
            rcases Nat.lt_or_ge 130316251073051 n with h12 | h12
            · -- n > 130316251073051
              exact RamareSaouter2003.prime_interval_nat_ladder_c03871 n (by omega) (by omega)
            · -- n <= 130316251073051
              exact RamareSaouter2003.prime_interval_nat_ladder_c03870 n (by omega) (by omega)
          · -- n <= 129994548862271
            exact RamareSaouter2003.prime_interval_nat_ladder_c03869 n (by omega) (by omega)
      · -- n <= 129673640814269
        rcases Nat.lt_or_ge 128715662065847 n with h8 | h8
        · -- n > 128715662065847
          rcases Nat.lt_or_ge 129034199369249 n with h10 | h10
          · -- n > 129034199369249
            rcases Nat.lt_or_ge 129353524968407 n with h12 | h12
            · -- n > 129353524968407
              exact RamareSaouter2003.prime_interval_nat_ladder_c03868 n (by omega) (by omega)
            · -- n <= 129353524968407
              exact RamareSaouter2003.prime_interval_nat_ladder_c03867 n (by omega) (by omega)
          · -- n <= 129034199369249
            exact RamareSaouter2003.prime_interval_nat_ladder_c03866 n (by omega) (by omega)
        · -- n <= 128715662065847
          rcases Nat.lt_or_ge 128080944567073 n with h10 | h10
          · -- n > 128080944567073
            rcases Nat.lt_or_ge 128397911112169 n with h12 | h12
            · -- n > 128397911112169
              exact RamareSaouter2003.prime_interval_nat_ladder_c03865 n (by omega) (by omega)
            · -- n <= 128397911112169
              exact RamareSaouter2003.prime_interval_nat_ladder_c03864 n (by omega) (by omega)
          · -- n <= 128080944567073
            exact RamareSaouter2003.prime_interval_nat_ladder_c03863 n (by omega) (by omega)
    · -- n <= 127764760494247
      rcases Nat.lt_or_ge 125883980134259 n with h6 | h6
      · -- n > 125883980134259
        rcases Nat.lt_or_ge 126820883816173 n with h8 | h8
        · -- n > 126820883816173
          rcases Nat.lt_or_ge 127134732043133 n with h10 | h10
          · -- n > 127134732043133
            rcases Nat.lt_or_ge 127449356961821 n with h12 | h12
            · -- n > 127449356961821
              exact RamareSaouter2003.prime_interval_nat_ladder_c03862 n (by omega) (by omega)
            · -- n <= 127449356961821
              exact RamareSaouter2003.prime_interval_nat_ladder_c03861 n (by omega) (by omega)
          · -- n <= 127134732043133
            exact RamareSaouter2003.prime_interval_nat_ladder_c03860 n (by omega) (by omega)
        · -- n <= 126820883816173
          rcases Nat.lt_or_ge 126195509772047 n with h10 | h10
          · -- n > 126195509772047
            rcases Nat.lt_or_ge 126507810363227 n with h12 | h12
            · -- n > 126507810363227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03859 n (by omega) (by omega)
            · -- n <= 126507810363227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03858 n (by omega) (by omega)
          · -- n <= 126195509772047
            exact RamareSaouter2003.prime_interval_nat_ladder_c03857 n (by omega) (by omega)
      · -- n <= 125883980134259
        rcases Nat.lt_or_ge 124953997934629 n with h8 | h8
        · -- n > 124953997934629
          rcases Nat.lt_or_ge 125263226111713 n with h10 | h10
          · -- n > 125263226111713
            rcases Nat.lt_or_ge 125573219546989 n with h12 | h12
            · -- n > 125573219546989
              exact RamareSaouter2003.prime_interval_nat_ladder_c03856 n (by omega) (by omega)
            · -- n <= 125573219546989
              exact RamareSaouter2003.prime_interval_nat_ladder_c03855 n (by omega) (by omega)
          · -- n <= 125263226111713
            exact RamareSaouter2003.prime_interval_nat_ladder_c03854 n (by omega) (by omega)
        · -- n <= 124953997934629
          rcases Nat.lt_or_ge 124337829802909 n with h10 | h10
          · -- n > 124337829802909
            rcases Nat.lt_or_ge 124645533126551 n with h12 | h12
            · -- n > 124645533126551
              exact RamareSaouter2003.prime_interval_nat_ladder_c03853 n (by omega) (by omega)
            · -- n <= 124645533126551
              exact RamareSaouter2003.prime_interval_nat_ladder_c03852 n (by omega) (by omega)
          · -- n <= 124337829802909
            exact RamareSaouter2003.prime_interval_nat_ladder_c03851 n (by omega) (by omega)
