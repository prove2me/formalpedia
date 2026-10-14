-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T19:12:20.231459+00:00
-- url     : https://prove2.me/submissions/419705c6-e129-4726-80af-7b89f76c4ffd

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05900

theorem solution (n : Nat)
    (hn : 34405922531916673 < n) (hupper : n <= 39629926580993773) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 36925659096654947 n with h2 | h2
  · -- n > 36925659096654947
    rcases Nat.lt_or_ge 38199857790185827 n with h4 | h4
    · -- n > 38199857790185827
      rcases Nat.lt_or_ge 38853377025471149 n with h6 | h6
      · -- n > 38853377025471149
        rcases Nat.lt_or_ge 39184311275198281 n with h8 | h8
        · -- n > 39184311275198281
          rcases Nat.lt_or_ge 39406480420720289 n with h10 | h10
          · -- n > 39406480420720289
            rcases Nat.lt_or_ge 39518048012470543 n with h12 | h12
            · -- n > 39518048012470543
              exact RamareSaouter2003.prime_interval_nat_ladder_c05900 n (by omega) (by omega)
            · -- n <= 39518048012470543
              exact RamareSaouter2003.prime_interval_nat_ladder_c05899 n (by omega) (by omega)
          · -- n <= 39406480420720289
            rcases Nat.lt_or_ge 39295240228549069 n with h12 | h12
            · -- n > 39295240228549069
              exact RamareSaouter2003.prime_interval_nat_ladder_c05898 n (by omega) (by omega)
            · -- n <= 39295240228549069
              exact RamareSaouter2003.prime_interval_nat_ladder_c05897 n (by omega) (by omega)
        · -- n <= 39184311275198281
          rcases Nat.lt_or_ge 38963382085320241 n with h10 | h10
          · -- n > 38963382085320241
            rcases Nat.lt_or_ge 39073696866490277 n with h12 | h12
            · -- n > 39073696866490277
              exact RamareSaouter2003.prime_interval_nat_ladder_c05896 n (by omega) (by omega)
            · -- n <= 39073696866490277
              exact RamareSaouter2003.prime_interval_nat_ladder_c05895 n (by omega) (by omega)
          · -- n <= 38963382085320241
            exact RamareSaouter2003.prime_interval_nat_ladder_c05894 n (by omega) (by omega)
      · -- n <= 38853377025471149
        rcases Nat.lt_or_ge 38525232276616249 n with h8 | h8
        · -- n > 38525232276616249
          rcases Nat.lt_or_ge 38634300414684781 n with h10 | h10
          · -- n > 38634300414684781
            rcases Nat.lt_or_ge 38743682167092943 n with h12 | h12
            · -- n > 38743682167092943
              exact RamareSaouter2003.prime_interval_nat_ladder_c05893 n (by omega) (by omega)
            · -- n <= 38743682167092943
              exact RamareSaouter2003.prime_interval_nat_ladder_c05892 n (by omega) (by omega)
          · -- n <= 38634300414684781
            exact RamareSaouter2003.prime_interval_nat_ladder_c05891 n (by omega) (by omega)
        · -- n <= 38525232276616249
          rcases Nat.lt_or_ge 38308007101061821 n with h10 | h10
          · -- n > 38308007101061821
            rcases Nat.lt_or_ge 38416466088786571 n with h12 | h12
            · -- n > 38416466088786571
              exact RamareSaouter2003.prime_interval_nat_ladder_c05890 n (by omega) (by omega)
            · -- n <= 38416466088786571
              exact RamareSaouter2003.prime_interval_nat_ladder_c05889 n (by omega) (by omega)
          · -- n <= 38308007101061821
            exact RamareSaouter2003.prime_interval_nat_ladder_c05888 n (by omega) (by omega)
    · -- n <= 38199857790185827
      rcases Nat.lt_or_ge 37557357555301853 n with h6 | h6
      · -- n > 37557357555301853
        rcases Nat.lt_or_ge 37877239514692577 n with h8 | h8
        · -- n > 37877239514692577
          rcases Nat.lt_or_ge 37984478159430029 n with h10 | h10
          · -- n > 37984478159430029
            rcases Nat.lt_or_ge 38092016726379661 n with h12 | h12
            · -- n > 38092016726379661
              exact RamareSaouter2003.prime_interval_nat_ladder_c05887 n (by omega) (by omega)
            · -- n <= 38092016726379661
              exact RamareSaouter2003.prime_interval_nat_ladder_c05886 n (by omega) (by omega)
          · -- n <= 37984478159430029
            exact RamareSaouter2003.prime_interval_nat_ladder_c05885 n (by omega) (by omega)
        · -- n <= 37877239514692577
          rcases Nat.lt_or_ge 37663670344069463 n with h10 | h10
          · -- n > 37663670344069463
            rcases Nat.lt_or_ge 37770304422766843 n with h12 | h12
            · -- n > 37770304422766843
              exact RamareSaouter2003.prime_interval_nat_ladder_c05884 n (by omega) (by omega)
            · -- n <= 37770304422766843
              exact RamareSaouter2003.prime_interval_nat_ladder_c05883 n (by omega) (by omega)
          · -- n <= 37663670344069463
            exact RamareSaouter2003.prime_interval_nat_ladder_c05882 n (by omega) (by omega)
      · -- n <= 37557357555301853
        rcases Nat.lt_or_ge 37240165901323043 n with h8 | h8
        · -- n > 37240165901323043
          rcases Nat.lt_or_ge 37345585816391519 n with h10 | h10
          · -- n > 37345585816391519
            rcases Nat.lt_or_ge 37451321570761027 n with h12 | h12
            · -- n > 37451321570761027
              exact RamareSaouter2003.prime_interval_nat_ladder_c05881 n (by omega) (by omega)
            · -- n <= 37451321570761027
              exact RamareSaouter2003.prime_interval_nat_ladder_c05880 n (by omega) (by omega)
          · -- n <= 37345585816391519
            exact RamareSaouter2003.prime_interval_nat_ladder_c05879 n (by omega) (by omega)
        · -- n <= 37240165901323043
          rcases Nat.lt_or_ge 37030183321906163 n with h10 | h10
          · -- n > 37030183321906163
            rcases Nat.lt_or_ge 37135025255179903 n with h12 | h12
            · -- n > 37135025255179903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05878 n (by omega) (by omega)
            · -- n <= 37135025255179903
              exact RamareSaouter2003.prime_interval_nat_ladder_c05877 n (by omega) (by omega)
          · -- n <= 37030183321906163
            exact RamareSaouter2003.prime_interval_nat_ladder_c05876 n (by omega) (by omega)
  · -- n <= 36925659096654947
    rcases Nat.lt_or_ge 35593190598185279 n with h4 | h4
    · -- n > 35593190598185279
      rcases Nat.lt_or_ge 36202083697388831 n with h6 | h6
      · -- n > 36202083697388831
        rcases Nat.lt_or_ge 36510438876912773 n with h8 | h8
        · -- n > 36510438876912773
          rcases Nat.lt_or_ge 36717469633778741 n with h10 | h10
          · -- n > 36717469633778741
            rcases Nat.lt_or_ge 36821419604434939 n with h12 | h12
            · -- n > 36821419604434939
              exact RamareSaouter2003.prime_interval_nat_ladder_c05875 n (by omega) (by omega)
            · -- n <= 36821419604434939
              exact RamareSaouter2003.prime_interval_nat_ladder_c05874 n (by omega) (by omega)
          · -- n <= 36717469633778741
            rcases Nat.lt_or_ge 36613810874045789 n with h12 | h12
            · -- n > 36613810874045789
              exact RamareSaouter2003.prime_interval_nat_ladder_c05873 n (by omega) (by omega)
            · -- n <= 36613810874045789
              exact RamareSaouter2003.prime_interval_nat_ladder_c05872 n (by omega) (by omega)
        · -- n <= 36510438876912773
          rcases Nat.lt_or_ge 36304581470987539 n with h10 | h10
          · -- n > 36304581470987539
            rcases Nat.lt_or_ge 36407366064492077 n with h12 | h12
            · -- n > 36407366064492077
              exact RamareSaouter2003.prime_interval_nat_ladder_c05871 n (by omega) (by omega)
            · -- n <= 36407366064492077
              exact RamareSaouter2003.prime_interval_nat_ladder_c05870 n (by omega) (by omega)
          · -- n <= 36304581470987539
            exact RamareSaouter2003.prime_interval_nat_ladder_c05869 n (by omega) (by omega)
      · -- n <= 36202083697388831
        rcases Nat.lt_or_ge 35896344243588359 n with h8 | h8
        · -- n > 35896344243588359
          rcases Nat.lt_or_ge 35997970295292329 n with h10 | h10
          · -- n > 35997970295292329
            rcases Nat.lt_or_ge 36099882108976663 n with h12 | h12
            · -- n > 36099882108976663
              exact RamareSaouter2003.prime_interval_nat_ladder_c05868 n (by omega) (by omega)
            · -- n <= 36099882108976663
              exact RamareSaouter2003.prime_interval_nat_ladder_c05867 n (by omega) (by omega)
          · -- n <= 35997970295292329
            exact RamareSaouter2003.prime_interval_nat_ladder_c05866 n (by omega) (by omega)
        · -- n <= 35896344243588359
          rcases Nat.lt_or_ge 35693963713371241 n with h10 | h10
          · -- n > 35693963713371241
            rcases Nat.lt_or_ge 35795009055059701 n with h12 | h12
            · -- n > 35795009055059701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05865 n (by omega) (by omega)
            · -- n <= 35795009055059701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05864 n (by omega) (by omega)
          · -- n <= 35693963713371241
            exact RamareSaouter2003.prime_interval_nat_ladder_c05863 n (by omega) (by omega)
    · -- n <= 35593190598185279
      rcases Nat.lt_or_ge 34994536940328341 n with h6 | h6
      · -- n > 34994536940328341
        rcases Nat.lt_or_ge 35292603712821551 n with h8 | h8
        · -- n > 35292603712821551
          rcases Nat.lt_or_ge 35392517617154111 n with h10 | h10
          · -- n > 35392517617154111
            rcases Nat.lt_or_ge 35492704999820801 n with h12 | h12
            · -- n > 35492704999820801
              exact RamareSaouter2003.prime_interval_nat_ladder_c05862 n (by omega) (by omega)
            · -- n <= 35492704999820801
              exact RamareSaouter2003.prime_interval_nat_ladder_c05861 n (by omega) (by omega)
          · -- n <= 35392517617154111
            exact RamareSaouter2003.prime_interval_nat_ladder_c05860 n (by omega) (by omega)
        · -- n <= 35292603712821551
          rcases Nat.lt_or_ge 35093609827660471 n with h10 | h10
          · -- n > 35093609827660471
            rcases Nat.lt_or_ge 35192968702186199 n with h12 | h12
            · -- n > 35192968702186199
              exact RamareSaouter2003.prime_interval_nat_ladder_c05859 n (by omega) (by omega)
            · -- n <= 35192968702186199
              exact RamareSaouter2003.prime_interval_nat_ladder_c05858 n (by omega) (by omega)
          · -- n <= 35093609827660471
            exact RamareSaouter2003.prime_interval_nat_ladder_c05857 n (by omega) (by omega)
      · -- n <= 34994536940328341
        rcases Nat.lt_or_ge 34698982970152507 n with h8 | h8
        · -- n > 34698982970152507
          rcases Nat.lt_or_ge 34797225764995301 n with h10 | h10
          · -- n > 34797225764995301
            rcases Nat.lt_or_ge 34895736702011039 n with h12 | h12
            · -- n > 34895736702011039
              exact RamareSaouter2003.prime_interval_nat_ladder_c05856 n (by omega) (by omega)
            · -- n <= 34895736702011039
              exact RamareSaouter2003.prime_interval_nat_ladder_c05855 n (by omega) (by omega)
          · -- n <= 34797225764995301
            exact RamareSaouter2003.prime_interval_nat_ladder_c05854 n (by omega) (by omega)
        · -- n <= 34698982970152507
          rcases Nat.lt_or_ge 34503331559801597 n with h10 | h10
          · -- n > 34503331559801597
            rcases Nat.lt_or_ge 34601017072434889 n with h12 | h12
            · -- n > 34601017072434889
              exact RamareSaouter2003.prime_interval_nat_ladder_c05853 n (by omega) (by omega)
            · -- n <= 34601017072434889
              exact RamareSaouter2003.prime_interval_nat_ladder_c05852 n (by omega) (by omega)
          · -- n <= 34503331559801597
            exact RamareSaouter2003.prime_interval_nat_ladder_c05851 n (by omega) (by omega)
