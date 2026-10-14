-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T03:29:24.540513+00:00
-- url     : https://prove2.me/submissions/40457b3c-cf35-4094-8f11-fd1491325d81

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07000

theorem solution (n : Nat)
    (hn : 771356764495307657 < n) (hupper : n <= 888481536827254001) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 827850458304847387 n with h2 | h2
  · -- n > 827850458304847387
    rcases Nat.lt_or_ge 856418846823705527 n with h4 | h4
    · -- n > 856418846823705527
      rcases Nat.lt_or_ge 871070663868652223 n with h6 | h6
      · -- n > 871070663868652223
        rcases Nat.lt_or_ge 878490207440326783 n with h8 | h8
        · -- n > 878490207440326783
          rcases Nat.lt_or_ge 883471760574018337 n with h10 | h10
          · -- n > 883471760574018337
            rcases Nat.lt_or_ge 885973102086575849 n with h12 | h12
            · -- n > 885973102086575849
              exact RamareSaouter2003.prime_interval_nat_ladder_c07000 n (by omega) (by omega)
            · -- n <= 885973102086575849
              exact RamareSaouter2003.prime_interval_nat_ladder_c06999 n (by omega) (by omega)
          · -- n <= 883471760574018337
            rcases Nat.lt_or_ge 880977446784596879 n with h12 | h12
            · -- n > 880977446784596879
              exact RamareSaouter2003.prime_interval_nat_ladder_c06998 n (by omega) (by omega)
            · -- n <= 880977446784596879
              exact RamareSaouter2003.prime_interval_nat_ladder_c06997 n (by omega) (by omega)
        · -- n <= 878490207440326783
          rcases Nat.lt_or_ge 873536892753426047 n with h10 | h10
          · -- n > 873536892753426047
            rcases Nat.lt_or_ge 876010005367519513 n with h12 | h12
            · -- n > 876010005367519513
              exact RamareSaouter2003.prime_interval_nat_ladder_c06996 n (by omega) (by omega)
            · -- n <= 876010005367519513
              exact RamareSaouter2003.prime_interval_nat_ladder_c06995 n (by omega) (by omega)
          · -- n <= 873536892753426047
            exact RamareSaouter2003.prime_interval_nat_ladder_c06994 n (by omega) (by omega)
      · -- n <= 871070663868652223
        rcases Nat.lt_or_ge 863713694404767643 n with h8 | h8
        · -- n > 863713694404767643
          rcases Nat.lt_or_ge 866159129750495873 n with h10 | h10
          · -- n > 866159129750495873
            rcases Nat.lt_or_ge 868611489081889559 n with h12 | h12
            · -- n > 868611489081889559
              exact RamareSaouter2003.prime_interval_nat_ladder_c06993 n (by omega) (by omega)
            · -- n <= 868611489081889559
              exact RamareSaouter2003.prime_interval_nat_ladder_c06992 n (by omega) (by omega)
          · -- n <= 866159129750495873
            exact RamareSaouter2003.prime_interval_nat_ladder_c06991 n (by omega) (by omega)
        · -- n <= 863713694404767643
          rcases Nat.lt_or_ge 858843568502901659 n with h10 | h10
          · -- n > 858843568502901659
            rcases Nat.lt_or_ge 861275166502460429 n with h12 | h12
            · -- n > 861275166502460429
              exact RamareSaouter2003.prime_interval_nat_ladder_c06990 n (by omega) (by omega)
            · -- n <= 861275166502460429
              exact RamareSaouter2003.prime_interval_nat_ladder_c06989 n (by omega) (by omega)
          · -- n <= 858843568502901659
            exact RamareSaouter2003.prime_interval_nat_ladder_c06988 n (by omega) (by omega)
    · -- n <= 856418846823705527
      rcases Nat.lt_or_ge 842013507434042591 n with h6 | h6
      · -- n > 842013507434042591
        rcases Nat.lt_or_ge 849185616454382443 n with h8 | h8
        · -- n > 849185616454382443
          rcases Nat.lt_or_ge 851589907384913371 n with h10 | h10
          · -- n > 851589907384913371
            rcases Nat.lt_or_ge 854000947978799287 n with h12 | h12
            · -- n > 854000947978799287
              exact RamareSaouter2003.prime_interval_nat_ladder_c06987 n (by omega) (by omega)
            · -- n <= 854000947978799287
              exact RamareSaouter2003.prime_interval_nat_ladder_c06986 n (by omega) (by omega)
          · -- n <= 851589907384913371
            exact RamareSaouter2003.prime_interval_nat_ladder_c06985 n (by omega) (by omega)
        · -- n <= 849185616454382443
          rcases Nat.lt_or_ge 844397452996003339 n with h10 | h10
          · -- n > 844397452996003339
            rcases Nat.lt_or_ge 846788162186529323 n with h12 | h12
            · -- n > 846788162186529323
              exact RamareSaouter2003.prime_interval_nat_ladder_c06984 n (by omega) (by omega)
            · -- n <= 846788162186529323
              exact RamareSaouter2003.prime_interval_nat_ladder_c06983 n (by omega) (by omega)
          · -- n <= 844397452996003339
            exact RamareSaouter2003.prime_interval_nat_ladder_c06982 n (by omega) (by omega)
      · -- n <= 842013507434042591
        rcases Nat.lt_or_ge 834901932405527923 n with h8 | h8
        · -- n > 834901932405527923
          rcases Nat.lt_or_ge 837265789765791733 n with h10 | h10
          · -- n > 837265789765791733
            rcases Nat.lt_or_ge 839636267243907479 n with h12 | h12
            · -- n > 839636267243907479
              exact RamareSaouter2003.prime_interval_nat_ladder_c06981 n (by omega) (by omega)
            · -- n <= 839636267243907479
              exact RamareSaouter2003.prime_interval_nat_ladder_c06980 n (by omega) (by omega)
          · -- n <= 837265789765791733
            exact RamareSaouter2003.prime_interval_nat_ladder_c06979 n (by omega) (by omega)
        · -- n <= 834901932405527923
          rcases Nat.lt_or_ge 830194323787427861 n with h10 | h10
          · -- n > 830194323787427861
            rcases Nat.lt_or_ge 832544769025234673 n with h12 | h12
            · -- n > 832544769025234673
              exact RamareSaouter2003.prime_interval_nat_ladder_c06978 n (by omega) (by omega)
            · -- n <= 832544769025234673
              exact RamareSaouter2003.prime_interval_nat_ladder_c06977 n (by omega) (by omega)
          · -- n <= 830194323787427861
            exact RamareSaouter2003.prime_interval_nat_ladder_c06976 n (by omega) (by omega)
  · -- n <= 827850458304847387
    rcases Nat.lt_or_ge 797975704979330819 n with h4 | h4
    · -- n > 797975704979330819
      rcases Nat.lt_or_ge 811627694640542051 n with h6 | h6
      · -- n > 811627694640542051
        rcases Nat.lt_or_ge 818541029539832671 n with h8 | h8
        · -- n > 818541029539832671
          rcases Nat.lt_or_ge 823182587832475669 n with h10 | h10
          · -- n > 823182587832475669
            rcases Nat.lt_or_ge 825513255284328383 n with h12 | h12
            · -- n > 825513255284328383
              exact RamareSaouter2003.prime_interval_nat_ladder_c06975 n (by omega) (by omega)
            · -- n <= 825513255284328383
              exact RamareSaouter2003.prime_interval_nat_ladder_c06974 n (by omega) (by omega)
          · -- n <= 823182587832475669
            rcases Nat.lt_or_ge 820858567453233047 n with h12 | h12
            · -- n > 820858567453233047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06973 n (by omega) (by omega)
            · -- n <= 820858567453233047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06972 n (by omega) (by omega)
        · -- n <= 818541029539832671
          rcases Nat.lt_or_ge 813925574554394573 n with h10 | h10
          · -- n > 813925574554394573
            rcases Nat.lt_or_ge 816230047381463669 n with h12 | h12
            · -- n > 816230047381463669
              exact RamareSaouter2003.prime_interval_nat_ladder_c06971 n (by omega) (by omega)
            · -- n <= 816230047381463669
              exact RamareSaouter2003.prime_interval_nat_ladder_c06970 n (by omega) (by omega)
          · -- n <= 813925574554394573
            exact RamareSaouter2003.prime_interval_nat_ladder_c06969 n (by omega) (by omega)
      · -- n <= 811627694640542051
        rcases Nat.lt_or_ge 804772682927284307 n with h8 | h8
        · -- n > 804772682927284307
          rcases Nat.lt_or_ge 807051230946931963 n with h10 | h10
          · -- n > 807051230946931963
            rcases Nat.lt_or_ge 809336235107741291 n with h12 | h12
            · -- n > 809336235107741291
              exact RamareSaouter2003.prime_interval_nat_ladder_c06968 n (by omega) (by omega)
            · -- n <= 809336235107741291
              exact RamareSaouter2003.prime_interval_nat_ladder_c06967 n (by omega) (by omega)
          · -- n <= 807051230946931963
            exact RamareSaouter2003.prime_interval_nat_ladder_c06966 n (by omega) (by omega)
        · -- n <= 804772682927284307
          rcases Nat.lt_or_ge 800234922021252433 n with h10 | h10
          · -- n > 800234922021252433
            rcases Nat.lt_or_ge 802500611369829557 n with h12 | h12
            · -- n > 802500611369829557
              exact RamareSaouter2003.prime_interval_nat_ladder_c06965 n (by omega) (by omega)
            · -- n <= 802500611369829557
              exact RamareSaouter2003.prime_interval_nat_ladder_c06964 n (by omega) (by omega)
          · -- n <= 800234922021252433
            exact RamareSaouter2003.prime_interval_nat_ladder_c06963 n (by omega) (by omega)
    · -- n <= 797975704979330819
      rcases Nat.lt_or_ge 784553386383421637 n with h6 | h6
      · -- n > 784553386383421637
        rcases Nat.lt_or_ge 791236026852631939 n with h8 | h8
        · -- n > 791236026852631939
          rcases Nat.lt_or_ge 793476247554528253 n with h10 | h10
          · -- n > 793476247554528253
            rcases Nat.lt_or_ge 795722778684896341 n with h12 | h12
            · -- n > 795722778684896341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06962 n (by omega) (by omega)
            · -- n <= 795722778684896341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06961 n (by omega) (by omega)
          · -- n <= 793476247554528253
            exact RamareSaouter2003.prime_interval_nat_ladder_c06960 n (by omega) (by omega)
        · -- n <= 791236026852631939
          rcases Nat.lt_or_ge 786774685182906509 n with h10 | h10
          · -- n > 786774685182906509
            rcases Nat.lt_or_ge 789002152899294617 n with h12 | h12
            · -- n > 789002152899294617
              exact RamareSaouter2003.prime_interval_nat_ladder_c06959 n (by omega) (by omega)
            · -- n <= 789002152899294617
              exact RamareSaouter2003.prime_interval_nat_ladder_c06958 n (by omega) (by omega)
          · -- n <= 786774685182906509
            exact RamareSaouter2003.prime_interval_nat_ladder_c06957 n (by omega) (by omega)
      · -- n <= 784553386383421637
        rcases Nat.lt_or_ge 777927075185066363 n with h8 | h8
        · -- n > 777927075185066363
          rcases Nat.lt_or_ge 780129622990672091 n with h10 | h10
          · -- n > 780129622990672091
            rcases Nat.lt_or_ge 782338390846855889 n with h12 | h12
            · -- n > 782338390846855889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06956 n (by omega) (by omega)
            · -- n <= 782338390846855889
              exact RamareSaouter2003.prime_interval_nat_ladder_c06955 n (by omega) (by omega)
          · -- n <= 780129622990672091
            exact RamareSaouter2003.prime_interval_nat_ladder_c06954 n (by omega) (by omega)
        · -- n <= 777927075185066363
          rcases Nat.lt_or_ge 773540696144587967 n with h10 | h10
          · -- n > 773540696144587967
            rcases Nat.lt_or_ge 775730820648028367 n with h12 | h12
            · -- n > 775730820648028367
              exact RamareSaouter2003.prime_interval_nat_ladder_c06953 n (by omega) (by omega)
            · -- n <= 775730820648028367
              exact RamareSaouter2003.prime_interval_nat_ladder_c06952 n (by omega) (by omega)
          · -- n <= 773540696144587967
            exact RamareSaouter2003.prime_interval_nat_ladder_c06951 n (by omega) (by omega)
