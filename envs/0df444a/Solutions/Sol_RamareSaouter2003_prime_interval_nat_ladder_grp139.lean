-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T03:07:01.49699+00:00
-- url     : https://prove2.me/submissions/fbf00e1f-58e6-402b-acb3-af6afd3c6077

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06950

theorem solution (n : Nat)
    (hn : 669672189073886627 < n) (hupper : n <= 771356764495307657) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 718718300983128293 n with h2 | h2
  · -- n > 718718300983128293
    rcases Nat.lt_or_ge 743520674148754141 n with h4 | h4
    · -- n > 743520674148754141
      rcases Nat.lt_or_ge 756240986073273277 n with h6 | h6
      · -- n > 756240986073273277
        rcases Nat.lt_or_ge 762682598916742201 n with h8 | h8
        · -- n > 762682598916742201
          rcases Nat.lt_or_ge 767007428918094757 n with h10 | h10
          · -- n > 767007428918094757
            rcases Nat.lt_or_ge 769179000245042159 n with h12 | h12
            · -- n > 769179000245042159
              exact RamareSaouter2003.prime_interval_nat_ladder_c06950 n (by omega) (by omega)
            · -- n <= 769179000245042159
              exact RamareSaouter2003.prime_interval_nat_ladder_c06949 n (by omega) (by omega)
          · -- n <= 767007428918094757
            rcases Nat.lt_or_ge 764841974296670833 n with h12 | h12
            · -- n > 764841974296670833
              exact RamareSaouter2003.prime_interval_nat_ladder_c06948 n (by omega) (by omega)
            · -- n <= 764841974296670833
              exact RamareSaouter2003.prime_interval_nat_ladder_c06947 n (by omega) (by omega)
        · -- n <= 762682598916742201
          rcases Nat.lt_or_ge 758382132577816547 n with h10 | h10
          · -- n > 758382132577816547
            rcases Nat.lt_or_ge 760529316281221843 n with h12 | h12
            · -- n > 760529316281221843
              exact RamareSaouter2003.prime_interval_nat_ladder_c06946 n (by omega) (by omega)
            · -- n <= 760529316281221843
              exact RamareSaouter2003.prime_interval_nat_ladder_c06945 n (by omega) (by omega)
          · -- n <= 758382132577816547
            exact RamareSaouter2003.prime_interval_nat_ladder_c06944 n (by omega) (by omega)
      · -- n <= 756240986073273277
        rcases Nat.lt_or_ge 749853793498004609 n with h8 | h8
        · -- n > 749853793498004609
          rcases Nat.lt_or_ge 751976821563866399 n with h10 | h10
          · -- n > 751976821563866399
            rcases Nat.lt_or_ge 754105884912626219 n with h12 | h12
            · -- n > 754105884912626219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06943 n (by omega) (by omega)
            · -- n <= 754105884912626219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06942 n (by omega) (by omega)
          · -- n <= 751976821563866399
            exact RamareSaouter2003.prime_interval_nat_ladder_c06941 n (by omega) (by omega)
        · -- n <= 749853793498004609
          rcases Nat.lt_or_ge 745625773166987017 n with h10 | h10
          · -- n > 745625773166987017
            rcases Nat.lt_or_ge 747736819158684673 n with h12 | h12
            · -- n > 747736819158684673
              exact RamareSaouter2003.prime_interval_nat_ladder_c06940 n (by omega) (by omega)
            · -- n <= 747736819158684673
              exact RamareSaouter2003.prime_interval_nat_ladder_c06939 n (by omega) (by omega)
          · -- n <= 745625773166987017
            exact RamareSaouter2003.prime_interval_nat_ladder_c06938 n (by omega) (by omega)
    · -- n <= 743520674148754141
      rcases Nat.lt_or_ge 731014320544315573 n with h6 | h6
      · -- n > 731014320544315573
        rcases Nat.lt_or_ge 737241031363899103 n with h8 | h8
        · -- n > 737241031363899103
          rcases Nat.lt_or_ge 739328373501848441 n with h10 | h10
          · -- n > 739328373501848441
            rcases Nat.lt_or_ge 741421544005418543 n with h12 | h12
            · -- n > 741421544005418543
              exact RamareSaouter2003.prime_interval_nat_ladder_c06937 n (by omega) (by omega)
            · -- n <= 741421544005418543
              exact RamareSaouter2003.prime_interval_nat_ladder_c06936 n (by omega) (by omega)
          · -- n <= 739328373501848441
            exact RamareSaouter2003.prime_interval_nat_ladder_c06935 n (by omega) (by omega)
        · -- n <= 737241031363899103
          rcases Nat.lt_or_ge 733084035341302699 n with h10 | h10
          · -- n > 733084035341302699
            rcases Nat.lt_or_ge 735159620359502941 n with h12 | h12
            · -- n > 735159620359502941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06934 n (by omega) (by omega)
            · -- n <= 735159620359502941
              exact RamareSaouter2003.prime_interval_nat_ladder_c06933 n (by omega) (by omega)
          · -- n <= 733084035341302699
            exact RamareSaouter2003.prime_interval_nat_ladder_c06932 n (by omega) (by omega)
      · -- n <= 731014320544315573
        rcases Nat.lt_or_ge 724840249009950001 n with h8 | h8
        · -- n > 724840249009950001
          rcases Nat.lt_or_ge 726892472118669613 n with h10 | h10
          · -- n > 726892472118669613
            rcases Nat.lt_or_ge 728950504506859259 n with h12 | h12
            · -- n > 728950504506859259
              exact RamareSaouter2003.prime_interval_nat_ladder_c06931 n (by omega) (by omega)
            · -- n <= 728950504506859259
              exact RamareSaouter2003.prime_interval_nat_ladder_c06930 n (by omega) (by omega)
          · -- n <= 726892472118669613
            exact RamareSaouter2003.prime_interval_nat_ladder_c06929 n (by omega) (by omega)
        · -- n <= 724840249009950001
          rcases Nat.lt_or_ge 720753185792563057 n with h10 | h10
          · -- n > 720753185792563057
            rcases Nat.lt_or_ge 722793810759381083 n with h12 | h12
            · -- n > 722793810759381083
              exact RamareSaouter2003.prime_interval_nat_ladder_c06928 n (by omega) (by omega)
            · -- n <= 722793810759381083
              exact RamareSaouter2003.prime_interval_nat_ladder_c06927 n (by omega) (by omega)
          · -- n <= 720753185792563057
            exact RamareSaouter2003.prime_interval_nat_ladder_c06926 n (by omega) (by omega)
  · -- n <= 718718300983128293
    rcases Nat.lt_or_ge 692782032476824867 n with h4 | h4
    · -- n > 692782032476824867
      rcases Nat.lt_or_ge 704634219214608821 n with h6 | h6
      · -- n > 704634219214608821
        rcases Nat.lt_or_ge 710636227291113581 n with h8 | h8
        · -- n > 710636227291113581
          rcases Nat.lt_or_ge 714665778563730319 n with h10 | h10
          · -- n > 714665778563730319
            rcases Nat.lt_or_ge 716689148929014137 n with h12 | h12
            · -- n > 716689148929014137
              exact RamareSaouter2003.prime_interval_nat_ladder_c06925 n (by omega) (by omega)
            · -- n <= 716689148929014137
              exact RamareSaouter2003.prime_interval_nat_ladder_c06924 n (by omega) (by omega)
          · -- n <= 714665778563730319
            rcases Nat.lt_or_ge 712648150530545003 n with h12 | h12
            · -- n > 712648150530545003
              exact RamareSaouter2003.prime_interval_nat_ladder_c06923 n (by omega) (by omega)
            · -- n <= 712648150530545003
              exact RamareSaouter2003.prime_interval_nat_ladder_c06922 n (by omega) (by omega)
        · -- n <= 710636227291113581
          rcases Nat.lt_or_ge 706629249944142089 n with h10 | h10
          · -- n > 706629249944142089
            rcases Nat.lt_or_ge 708629915843868899 n with h12 | h12
            · -- n > 708629915843868899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06921 n (by omega) (by omega)
            · -- n <= 708629915843868899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06920 n (by omega) (by omega)
          · -- n <= 706629249944142089
            exact RamareSaouter2003.prime_interval_nat_ladder_c06919 n (by omega) (by omega)
      · -- n <= 704634219214608821
        rcases Nat.lt_or_ge 698683088862491899 n with h8 | h8
        · -- n > 698683088862491899
          rcases Nat.lt_or_ge 700661241966379571 n with h10 | h10
          · -- n > 700661241966379571
            rcases Nat.lt_or_ge 702644909097444343 n with h12 | h12
            · -- n > 702644909097444343
              exact RamareSaouter2003.prime_interval_nat_ladder_c06918 n (by omega) (by omega)
            · -- n <= 702644909097444343
              exact RamareSaouter2003.prime_interval_nat_ladder_c06917 n (by omega) (by omega)
          · -- n <= 700661241966379571
            exact RamareSaouter2003.prime_interval_nat_ladder_c06916 n (by omega) (by omega)
        · -- n <= 698683088862491899
          rcases Nat.lt_or_ge 694743478351687703 n with h10 | h10
          · -- n > 694743478351687703
            rcases Nat.lt_or_ge 696710508248847601 n with h12 | h12
            · -- n > 696710508248847601
              exact RamareSaouter2003.prime_interval_nat_ladder_c06915 n (by omega) (by omega)
            · -- n <= 696710508248847601
              exact RamareSaouter2003.prime_interval_nat_ladder_c06914 n (by omega) (by omega)
          · -- n <= 694743478351687703
            exact RamareSaouter2003.prime_interval_nat_ladder_c06913 n (by omega) (by omega)
    · -- n <= 692782032476824867
      rcases Nat.lt_or_ge 681129119489376373 n with h6 | h6
      · -- n > 681129119489376373
        rcases Nat.lt_or_ge 686930852965540957 n with h8 | h8
        · -- n > 686930852965540957
          rcases Nat.lt_or_ge 688875765605731579 n with h10 | h10
          · -- n > 688875765605731579
            rcases Nat.lt_or_ge 690826152141119173 n with h12 | h12
            · -- n > 690826152141119173
              exact RamareSaouter2003.prime_interval_nat_ladder_c06912 n (by omega) (by omega)
            · -- n <= 690826152141119173
              exact RamareSaouter2003.prime_interval_nat_ladder_c06911 n (by omega) (by omega)
          · -- n <= 688875765605731579
            exact RamareSaouter2003.prime_interval_nat_ladder_c06910 n (by omega) (by omega)
        · -- n <= 686930852965540957
          rcases Nat.lt_or_ge 683057587143412903 n with h10 | h10
          · -- n > 683057587143412903
            rcases Nat.lt_or_ge 684991508776141913 n with h12 | h12
            · -- n > 684991508776141913
              exact RamareSaouter2003.prime_interval_nat_ladder_c06909 n (by omega) (by omega)
            · -- n <= 684991508776141913
              exact RamareSaouter2003.prime_interval_nat_ladder_c06908 n (by omega) (by omega)
          · -- n <= 683057587143412903
            exact RamareSaouter2003.prime_interval_nat_ladder_c06907 n (by omega) (by omega)
      · -- n <= 681129119489376373
        rcases Nat.lt_or_ge 675376320722271653 n with h8 | h8
        · -- n > 675376320722271653
          rcases Nat.lt_or_ge 677288511840573419 n with h10 | h10
          · -- n > 677288511840573419
            rcases Nat.lt_or_ge 679206122431679411 n with h12 | h12
            · -- n > 679206122431679411
              exact RamareSaouter2003.prime_interval_nat_ladder_c06906 n (by omega) (by omega)
            · -- n <= 679206122431679411
              exact RamareSaouter2003.prime_interval_nat_ladder_c06905 n (by omega) (by omega)
          · -- n <= 677288511840573419
            exact RamareSaouter2003.prime_interval_nat_ladder_c06904 n (by omega) (by omega)
        · -- n <= 675376320722271653
          rcases Nat.lt_or_ge 671568213461369723 n with h10 | h10
          · -- n > 671568213461369723
            rcases Nat.lt_or_ge 673469608258425791 n with h12 | h12
            · -- n > 673469608258425791
              exact RamareSaouter2003.prime_interval_nat_ladder_c06903 n (by omega) (by omega)
            · -- n <= 673469608258425791
              exact RamareSaouter2003.prime_interval_nat_ladder_c06902 n (by omega) (by omega)
          · -- n <= 671568213461369723
            exact RamareSaouter2003.prime_interval_nat_ladder_c06901 n (by omega) (by omega)
