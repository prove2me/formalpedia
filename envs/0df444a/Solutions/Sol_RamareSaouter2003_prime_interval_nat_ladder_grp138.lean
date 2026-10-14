-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T02:51:23.342767+00:00
-- url     : https://prove2.me/submissions/8753b128-9ff8-4df0-b743-e2ecdf2d638e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06900

theorem solution (n : Nat)
    (hn : 581391753836179799 < n) (hupper : n <= 669672189073886627) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 623972542918763231 n with h2 | h2
  · -- n > 623972542918763231
    rcases Nat.lt_or_ge 645505474295806057 n with h4 | h4
    · -- n > 645505474295806057
      rcases Nat.lt_or_ge 656549084568346751 n with h6 | h6
      · -- n > 656549084568346751
        rcases Nat.lt_or_ge 662141445766269263 n with h8 | h8
        · -- n > 662141445766269263
          rcases Nat.lt_or_ge 665896187835789353 n with h10 | h10
          · -- n > 665896187835789353
            rcases Nat.lt_or_ge 667781533458906677 n with h12 | h12
            · -- n > 667781533458906677
              exact RamareSaouter2003.prime_interval_nat_ladder_c06900 n (by omega) (by omega)
            · -- n <= 667781533458906677
              exact RamareSaouter2003.prime_interval_nat_ladder_c06899 n (by omega) (by omega)
          · -- n <= 665896187835789353
            rcases Nat.lt_or_ge 664016167311047893 n with h12 | h12
            · -- n > 664016167311047893
              exact RamareSaouter2003.prime_interval_nat_ladder_c06898 n (by omega) (by omega)
            · -- n <= 664016167311047893
              exact RamareSaouter2003.prime_interval_nat_ladder_c06897 n (by omega) (by omega)
        · -- n <= 662141445766269263
          rcases Nat.lt_or_ge 658407932604854879 n with h10 | h10
          · -- n > 658407932604854879
            rcases Nat.lt_or_ge 660272016835653491 n with h12 | h12
            · -- n > 660272016835653491
              exact RamareSaouter2003.prime_interval_nat_ladder_c06896 n (by omega) (by omega)
            · -- n <= 660272016835653491
              exact RamareSaouter2003.prime_interval_nat_ladder_c06895 n (by omega) (by omega)
          · -- n <= 658407932604854879
            exact RamareSaouter2003.prime_interval_nat_ladder_c06894 n (by omega) (by omega)
      · -- n <= 656549084568346751
        rcases Nat.lt_or_ge 651003849589175833 n with h8 | h8
        · -- n > 651003849589175833
          rcases Nat.lt_or_ge 652847031372457591 n with h10 | h10
          · -- n > 652847031372457591
            rcases Nat.lt_or_ge 654695440469464099 n with h12 | h12
            · -- n > 654695440469464099
              exact RamareSaouter2003.prime_interval_nat_ladder_c06893 n (by omega) (by omega)
            · -- n <= 654695440469464099
              exact RamareSaouter2003.prime_interval_nat_ladder_c06892 n (by omega) (by omega)
          · -- n <= 652847031372457591
            exact RamareSaouter2003.prime_interval_nat_ladder_c06891 n (by omega) (by omega)
        · -- n <= 651003849589175833
          rcases Nat.lt_or_ge 647333090849039821 n with h10 | h10
          · -- n > 647333090849039821
            rcases Nat.lt_or_ge 649165888663183729 n with h12 | h12
            · -- n > 649165888663183729
              exact RamareSaouter2003.prime_interval_nat_ladder_c06890 n (by omega) (by omega)
            · -- n <= 649165888663183729
              exact RamareSaouter2003.prime_interval_nat_ladder_c06889 n (by omega) (by omega)
          · -- n <= 647333090849039821
            exact RamareSaouter2003.prime_interval_nat_ladder_c06888 n (by omega) (by omega)
    · -- n <= 645505474295806057
      rcases Nat.lt_or_ge 634647678988563829 n with h6 | h6
      · -- n > 634647678988563829
        rcases Nat.lt_or_ge 640053555581840921 n with h8 | h8
        · -- n > 640053555581840921
          rcases Nat.lt_or_ge 641865705616286147 n with h10 | h10
          · -- n > 641865705616286147
            rcases Nat.lt_or_ge 643683013566513961 n with h12 | h12
            · -- n > 643683013566513961
              exact RamareSaouter2003.prime_interval_nat_ladder_c06887 n (by omega) (by omega)
            · -- n <= 643683013566513961
              exact RamareSaouter2003.prime_interval_nat_ladder_c06886 n (by omega) (by omega)
          · -- n <= 641865705616286147
            exact RamareSaouter2003.prime_interval_nat_ladder_c06885 n (by omega) (by omega)
        · -- n <= 640053555581840921
          rcases Nat.lt_or_ge 636444548273773247 n with h10 | h10
          · -- n > 636444548273773247
            rcases Nat.lt_or_ge 638246506279632461 n with h12 | h12
            · -- n > 638246506279632461
              exact RamareSaouter2003.prime_interval_nat_ladder_c06884 n (by omega) (by omega)
            · -- n <= 638246506279632461
              exact RamareSaouter2003.prime_interval_nat_ladder_c06883 n (by omega) (by omega)
          · -- n <= 636444548273773247
            exact RamareSaouter2003.prime_interval_nat_ladder_c06882 n (by omega) (by omega)
      · -- n <= 634647678988563829
        rcases Nat.lt_or_ge 629287477613037587 n with h8 | h8
        · -- n > 629287477613037587
          rcases Nat.lt_or_ge 631069177457893219 n with h10 | h10
          · -- n > 631069177457893219
            rcases Nat.lt_or_ge 632855882756413891 n with h12 | h12
            · -- n > 632855882756413891
              exact RamareSaouter2003.prime_interval_nat_ladder_c06881 n (by omega) (by omega)
            · -- n <= 632855882756413891
              exact RamareSaouter2003.prime_interval_nat_ladder_c06880 n (by omega) (by omega)
          · -- n <= 631069177457893219
            exact RamareSaouter2003.prime_interval_nat_ladder_c06879 n (by omega) (by omega)
        · -- n <= 629287477613037587
          rcases Nat.lt_or_ge 625739166269349409 n with h10 | h10
          · -- n > 625739166269349409
            rcases Nat.lt_or_ge 627510815544863603 n with h12 | h12
            · -- n > 627510815544863603
              exact RamareSaouter2003.prime_interval_nat_ladder_c06878 n (by omega) (by omega)
            · -- n <= 627510815544863603
              exact RamareSaouter2003.prime_interval_nat_ladder_c06877 n (by omega) (by omega)
          · -- n <= 625739166269349409
            exact RamareSaouter2003.prime_interval_nat_ladder_c06876 n (by omega) (by omega)
  · -- n <= 623972542918763231
    rcases Nat.lt_or_ge 601455061496755519 n with h4 | h4
    · -- n > 601455061496755519
      rcases Nat.lt_or_ge 611744908013686679 n with h6 | h6
      · -- n > 611744908013686679
        rcases Nat.lt_or_ge 616955692579240249 n with h8 | h8
        · -- n > 616955692579240249
          rcases Nat.lt_or_ge 620454194056378433 n with h10 | h10
          · -- n > 620454194056378433
            rcases Nat.lt_or_ge 622210881115916507 n with h12 | h12
            · -- n > 622210881115916507
              exact RamareSaouter2003.prime_interval_nat_ladder_c06875 n (by omega) (by omega)
            · -- n <= 622210881115916507
              exact RamareSaouter2003.prime_interval_nat_ladder_c06874 n (by omega) (by omega)
          · -- n <= 620454194056378433
            rcases Nat.lt_or_ge 618702474300448061 n with h12 | h12
            · -- n > 618702474300448061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06873 n (by omega) (by omega)
            · -- n <= 618702474300448061
              exact RamareSaouter2003.prime_interval_nat_ladder_c06872 n (by omega) (by omega)
        · -- n <= 616955692579240249
          rcases Nat.lt_or_ge 613476910490612953 n with h10 | h10
          · -- n > 613476910490612953
            rcases Nat.lt_or_ge 615213838261824203 n with h12 | h12
            · -- n > 615213838261824203
              exact RamareSaouter2003.prime_interval_nat_ladder_c06871 n (by omega) (by omega)
            · -- n <= 615213838261824203
              exact RamareSaouter2003.prime_interval_nat_ladder_c06870 n (by omega) (by omega)
          · -- n <= 613476910490612953
            exact RamareSaouter2003.prime_interval_nat_ladder_c06869 n (by omega) (by omega)
      · -- n <= 611744908013686679
        rcases Nat.lt_or_ge 606578237790704149 n with h8 | h8
        · -- n > 606578237790704149
          rcases Nat.lt_or_ge 608295625012463867 n with h10 | h10
          · -- n > 608295625012463867
            rcases Nat.lt_or_ge 610017884524468489 n with h12 | h12
            · -- n > 610017884524468489
              exact RamareSaouter2003.prime_interval_nat_ladder_c06868 n (by omega) (by omega)
            · -- n <= 610017884524468489
              exact RamareSaouter2003.prime_interval_nat_ladder_c06867 n (by omega) (by omega)
          · -- n <= 608295625012463867
            exact RamareSaouter2003.prime_interval_nat_ladder_c06866 n (by omega) (by omega)
        · -- n <= 606578237790704149
          rcases Nat.lt_or_ge 603157960074432979 n with h10 | h10
          · -- n > 603157960074432979
            rcases Nat.lt_or_ge 604865681599229933 n with h12 | h12
            · -- n > 604865681599229933
              exact RamareSaouter2003.prime_interval_nat_ladder_c06865 n (by omega) (by omega)
            · -- n <= 604865681599229933
              exact RamareSaouter2003.prime_interval_nat_ladder_c06864 n (by omega) (by omega)
          · -- n <= 603157960074432979
            exact RamareSaouter2003.prime_interval_nat_ladder_c06863 n (by omega) (by omega)
    · -- n <= 601455061496755519
      rcases Nat.lt_or_ge 591338284622405297 n with h6 | h6
      · -- n > 591338284622405297
        rcases Nat.lt_or_ge 596375187213610799 n with h8 | h8
        · -- n > 596375187213610799
          rcases Nat.lt_or_ge 598063676744247589 n with h10 | h10
          · -- n > 598063676744247589
            rcases Nat.lt_or_ge 599756969378068919 n with h12 | h12
            · -- n > 599756969378068919
              exact RamareSaouter2003.prime_interval_nat_ladder_c06862 n (by omega) (by omega)
            · -- n <= 599756969378068919
              exact RamareSaouter2003.prime_interval_nat_ladder_c06861 n (by omega) (by omega)
          · -- n <= 598063676744247589
            exact RamareSaouter2003.prime_interval_nat_ladder_c06860 n (by omega) (by omega)
        · -- n <= 596375187213610799
          rcases Nat.lt_or_ge 593012522847003869 n with h10 | h10
          · -- n > 593012522847003869
            rcases Nat.lt_or_ge 594691499893576529 n with h12 | h12
            · -- n > 594691499893576529
              exact RamareSaouter2003.prime_interval_nat_ladder_c06859 n (by omega) (by omega)
            · -- n <= 594691499893576529
              exact RamareSaouter2003.prime_interval_nat_ladder_c06858 n (by omega) (by omega)
          · -- n <= 593012522847003869
            exact RamareSaouter2003.prime_interval_nat_ladder_c06857 n (by omega) (by omega)
      · -- n <= 591338284622405297
        rcases Nat.lt_or_ge 586343962612248559 n with h8 | h8
        · -- n > 586343962612248559
          rcases Nat.lt_or_ge 588004075130276683 n with h10 | h10
          · -- n > 588004075130276683
            rcases Nat.lt_or_ge 589668872009602519 n with h12 | h12
            · -- n > 589668872009602519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06856 n (by omega) (by omega)
            · -- n <= 589668872009602519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06855 n (by omega) (by omega)
          · -- n <= 588004075130276683
            exact RamareSaouter2003.prime_interval_nat_ladder_c06854 n (by omega) (by omega)
        · -- n <= 586343962612248559
          rcases Nat.lt_or_ge 583037847007938689 n with h10 | h10
          · -- n > 583037847007938689
            rcases Nat.lt_or_ge 584688585644848957 n with h12 | h12
            · -- n > 584688585644848957
              exact RamareSaouter2003.prime_interval_nat_ladder_c06853 n (by omega) (by omega)
            · -- n <= 584688585644848957
              exact RamareSaouter2003.prime_interval_nat_ladder_c06852 n (by omega) (by omega)
          · -- n <= 583037847007938689
            exact RamareSaouter2003.prime_interval_nat_ladder_c06851 n (by omega) (by omega)
