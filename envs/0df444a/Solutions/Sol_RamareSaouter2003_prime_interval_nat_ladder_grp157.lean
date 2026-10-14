-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T09:56:23.976778+00:00
-- url     : https://prove2.me/submissions/dcc24f4a-700a-4a05-8b29-709126b513eb

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07800
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07835

theorem solution (n : Nat)
    (hn : 8198927391296255473 < n) (hupper : n <= 9417226134267899261) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 8774574860431075067 n with h2 | h2
  · -- n > 8774574860431075067
    rcases Nat.lt_or_ge 9077381944440643313 n with h4 | h4
    · -- n > 9077381944440643313
      rcases Nat.lt_or_ge 9232681667700063179 n with h6 | h6
      · -- n > 9232681667700063179
        rcases Nat.lt_or_ge 9311325201252476767 n with h8 | h8
        · -- n > 9311325201252476767
          rcases Nat.lt_or_ge 9364125833632411397 n with h10 | h10
          · -- n > 9364125833632411397
            rcases Nat.lt_or_ge 9390638500306986007 n with h12 | h12
            · -- n > 9390638500306986007
              exact RamareSaouter2003.prime_interval_nat_ladder_c07835 n (by omega) (by omega)
            · -- n <= 9390638500306986007
              exact RamareSaouter2003.prime_interval_nat_ladder_c07834 n (by omega) (by omega)
          · -- n <= 9364125833632411397
            rcases Nat.lt_or_ge 9337688299926851149 n with h12 | h12
            · -- n > 9337688299926851149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07833 n (by omega) (by omega)
            · -- n <= 9337688299926851149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07832 n (by omega) (by omega)
        · -- n <= 9311325201252476767
          rcases Nat.lt_or_ge 9258822140821453789 n with h10 | h10
          · -- n > 9258822140821453789
            rcases Nat.lt_or_ge 9285036711323785561 n with h12 | h12
            · -- n > 9285036711323785561
              exact RamareSaouter2003.prime_interval_nat_ladder_c07831 n (by omega) (by omega)
            · -- n <= 9285036711323785561
              exact RamareSaouter2003.prime_interval_nat_ladder_c07830 n (by omega) (by omega)
          · -- n <= 9258822140821453789
            exact RamareSaouter2003.prime_interval_nat_ladder_c07829 n (by omega) (by omega)
      · -- n <= 9232681667700063179
        rcases Nat.lt_or_ge 9154702316844721919 n with h8 | h8
        · -- n > 9154702316844721919
          rcases Nat.lt_or_ge 9180622048837940273 n with h10 | h10
          · -- n > 9180622048837940273
            rcases Nat.lt_or_ge 9206615166332339827 n with h12 | h12
            · -- n > 9206615166332339827
              exact RamareSaouter2003.prime_interval_nat_ladder_c07828 n (by omega) (by omega)
            · -- n <= 9206615166332339827
              exact RamareSaouter2003.prime_interval_nat_ladder_c07827 n (by omega) (by omega)
          · -- n <= 9180622048837940273
            exact RamareSaouter2003.prime_interval_nat_ladder_c07826 n (by omega) (by omega)
        · -- n <= 9154702316844721919
          rcases Nat.lt_or_ge 9103082637282072001 n with h10 | h10
          · -- n > 9103082637282072001
            rcases Nat.lt_or_ge 9128856069248355529 n with h12 | h12
            · -- n > 9128856069248355529
              exact RamareSaouter2003.prime_interval_nat_ladder_c07825 n (by omega) (by omega)
            · -- n <= 9128856069248355529
              exact RamareSaouter2003.prime_interval_nat_ladder_c07824 n (by omega) (by omega)
          · -- n <= 9103082637282072001
            exact RamareSaouter2003.prime_interval_nat_ladder_c07823 n (by omega) (by omega)
    · -- n <= 9077381944440643313
      rcases Nat.lt_or_ge 8924694313070028349 n with h6 | h6
      · -- n > 8924694313070028349
        rcases Nat.lt_or_ge 9000714349103767949 n with h8 | h8
        · -- n > 9000714349103767949
          rcases Nat.lt_or_ge 9026198035113792083 n with h10 | h10
          · -- n > 9026198035113792083
            rcases Nat.lt_or_ge 9051753656294805649 n with h12 | h12
            · -- n > 9051753656294805649
              exact RamareSaouter2003.prime_interval_nat_ladder_c07822 n (by omega) (by omega)
            · -- n <= 9051753656294805649
              exact RamareSaouter2003.prime_interval_nat_ladder_c07821 n (by omega) (by omega)
          · -- n <= 9026198035113792083
            exact RamareSaouter2003.prime_interval_nat_ladder_c07820 n (by omega) (by omega)
        · -- n <= 9000714349103767949
          rcases Nat.lt_or_ge 8949962733380481469 n with h10 | h10
          · -- n > 8949962733380481469
            rcases Nat.lt_or_ge 8975302572465320867 n with h12 | h12
            · -- n > 8975302572465320867
              exact RamareSaouter2003.prime_interval_nat_ladder_c07819 n (by omega) (by omega)
            · -- n <= 8975302572465320867
              exact RamareSaouter2003.prime_interval_nat_ladder_c07818 n (by omega) (by omega)
          · -- n <= 8949962733380481469
            exact RamareSaouter2003.prime_interval_nat_ladder_c07817 n (by omega) (by omega)
      · -- n <= 8924694313070028349
        rcases Nat.lt_or_ge 8849316280445905721 n with h8 | h8
        · -- n > 8849316280445905721
          rcases Nat.lt_or_ge 8874371401373672539 n with h10 | h10
          · -- n > 8874371401373672539
            rcases Nat.lt_or_ge 8899497310715226763 n with h12 | h12
            · -- n > 8899497310715226763
              exact RamareSaouter2003.prime_interval_nat_ladder_c07816 n (by omega) (by omega)
            · -- n <= 8899497310715226763
              exact RamareSaouter2003.prime_interval_nat_ladder_c07815 n (by omega) (by omega)
          · -- n <= 8874371401373672539
            exact RamareSaouter2003.prime_interval_nat_ladder_c07814 n (by omega) (by omega)
        · -- n <= 8849316280445905721
          rcases Nat.lt_or_ge 8799418088362987117 n with h10 | h10
          · -- n > 8799418088362987117
            rcases Nat.lt_or_ge 8824331934311928823 n with h12 | h12
            · -- n > 8824331934311928823
              exact RamareSaouter2003.prime_interval_nat_ladder_c07813 n (by omega) (by omega)
            · -- n <= 8824331934311928823
              exact RamareSaouter2003.prime_interval_nat_ladder_c07812 n (by omega) (by omega)
          · -- n <= 8799418088362987117
            exact RamareSaouter2003.prime_interval_nat_ladder_c07811 n (by omega) (by omega)
  · -- n <= 8774574860431075067
    rcases Nat.lt_or_ge 8481869152158087271 n with h4 | h4
    · -- n > 8481869152158087271
      rcases Nat.lt_or_ge 8626980190015020293 n with h6 | h6
      · -- n > 8626980190015020293
        rcases Nat.lt_or_ge 8700464596186241369 n with h8 | h8
        · -- n > 8700464596186241369
          rcases Nat.lt_or_ge 8725098090710973949 n with h10 | h10
          · -- n > 8725098090710973949
            rcases Nat.lt_or_ge 8749801502223680411 n with h12 | h12
            · -- n > 8749801502223680411
              exact RamareSaouter2003.prime_interval_nat_ladder_c07810 n (by omega) (by omega)
            · -- n <= 8749801502223680411
              exact RamareSaouter2003.prime_interval_nat_ladder_c07809 n (by omega) (by omega)
          · -- n <= 8725098090710973949
            exact RamareSaouter2003.prime_interval_nat_ladder_c07808 n (by omega) (by omega)
        · -- n <= 8700464596186241369
          rcases Nat.lt_or_ge 8651405780770589087 n with h10 | h10
          · -- n > 8651405780770589087
            rcases Nat.lt_or_ge 8675900569296012089 n with h12 | h12
            · -- n > 8675900569296012089
              exact RamareSaouter2003.prime_interval_nat_ladder_c07807 n (by omega) (by omega)
            · -- n <= 8675900569296012089
              exact RamareSaouter2003.prime_interval_nat_ladder_c07806 n (by omega) (by omega)
          · -- n <= 8651405780770589087
            exact RamareSaouter2003.prime_interval_nat_ladder_c07805 n (by omega) (by omega)
      · -- n <= 8626980190015020293
        rcases Nat.lt_or_ge 8554116966875175889 n with h8 | h8
        · -- n > 8554116966875175889
          rcases Nat.lt_or_ge 8578335832538073383 n with h10 | h10
          · -- n > 8578335832538073383
            rcases Nat.lt_or_ge 8602623597204935743 n with h12 | h12
            · -- n > 8602623597204935743
              exact RamareSaouter2003.prime_interval_nat_ladder_c07804 n (by omega) (by omega)
            · -- n <= 8602623597204935743
              exact RamareSaouter2003.prime_interval_nat_ladder_c07803 n (by omega) (by omega)
          · -- n <= 8578335832538073383
            exact RamareSaouter2003.prime_interval_nat_ladder_c07802 n (by omega) (by omega)
        · -- n <= 8554116966875175889
          rcases Nat.lt_or_ge 8505883858530145649 n with h10 | h10
          · -- n > 8505883858530145649
            rcases Nat.lt_or_ge 8529966468269729377 n with h12 | h12
            · -- n > 8529966468269729377
              exact RamareSaouter2003.prime_interval_nat_ladder_c07801 n (by omega) (by omega)
            · -- n <= 8529966468269729377
              exact RamareSaouter2003.prime_interval_nat_ladder_c07800 n (by omega) (by omega)
          · -- n <= 8505883858530145649
            exact RamareSaouter2003.prime_interval_nat_ladder_c07799 n (by omega) (by omega)
    · -- n <= 8481869152158087271
      rcases Nat.lt_or_ge 8339198360907826031 n with h6 | h6
      · -- n > 8339198360907826031
        rcases Nat.lt_or_ge 8410231411764896059 n with h8 | h8
        · -- n > 8410231411764896059
          rcases Nat.lt_or_ge 8434043363078865991 n with h10 | h10
          · -- n > 8434043363078865991
            rcases Nat.lt_or_ge 8457922444093513003 n with h12 | h12
            · -- n > 8457922444093513003
              exact RamareSaouter2003.prime_interval_nat_ladder_c07798 n (by omega) (by omega)
            · -- n <= 8457922444093513003
              exact RamareSaouter2003.prime_interval_nat_ladder_c07797 n (by omega) (by omega)
          · -- n <= 8434043363078865991
            exact RamareSaouter2003.prime_interval_nat_ladder_c07796 n (by omega) (by omega)
        · -- n <= 8410231411764896059
          rcases Nat.lt_or_ge 8362809114086696519 n with h10 | h10
          · -- n > 8362809114086696519
            rcases Nat.lt_or_ge 8386486767779204983 n with h12 | h12
            · -- n > 8386486767779204983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07795 n (by omega) (by omega)
            · -- n <= 8386486767779204983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07794 n (by omega) (by omega)
          · -- n <= 8362809114086696519
            exact RamareSaouter2003.prime_interval_nat_ladder_c07793 n (by omega) (by omega)
      · -- n <= 8339198360907826031
        rcases Nat.lt_or_ge 8268765329335556503 n with h8 | h8
        · -- n > 8268765329335556503
          rcases Nat.lt_or_ge 8292176736457131799 n with h10 | h10
          · -- n > 8292176736457131799
            rcases Nat.lt_or_ge 8315654291688694619 n with h12 | h12
            · -- n > 8315654291688694619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07792 n (by omega) (by omega)
            · -- n <= 8315654291688694619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07791 n (by omega) (by omega)
          · -- n <= 8292176736457131799
            exact RamareSaouter2003.prime_interval_nat_ladder_c07790 n (by omega) (by omega)
        · -- n <= 8268765329335556503
          rcases Nat.lt_or_ge 8222140825583360899 n with h10 | h10
          · -- n > 8222140825583360899
            rcases Nat.lt_or_ge 8245420189445418157 n with h12 | h12
            · -- n > 8245420189445418157
              exact RamareSaouter2003.prime_interval_nat_ladder_c07789 n (by omega) (by omega)
            · -- n <= 8245420189445418157
              exact RamareSaouter2003.prime_interval_nat_ladder_c07788 n (by omega) (by omega)
          · -- n <= 8222140825583360899
            exact RamareSaouter2003.prime_interval_nat_ladder_c07787 n (by omega) (by omega)
