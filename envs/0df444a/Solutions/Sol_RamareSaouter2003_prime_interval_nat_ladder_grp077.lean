-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T07:28:58.688303+00:00
-- url     : https://prove2.me/submissions/98db7c3d-23c7-4e6d-9dac-c8ae7079dbfa

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03850

theorem solution (n : Nat)
    (hn : 109611978750817 < n) (hupper : n <= 124030886084041) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 116598760069697 n with h2 | h2
  · -- n > 116598760069697
    rcases Nat.lt_or_ge 120108894845663 n with h4 | h4
    · -- n > 120108894845663
      rcases Nat.lt_or_ge 121903392050807 n with h6 | h6
      · -- n > 121903392050807
        rcases Nat.lt_or_ge 122810669821589 n with h8 | h8
        · -- n > 122810669821589
          rcases Nat.lt_or_ge 123419269964407 n with h10 | h10
          · -- n > 123419269964407
            rcases Nat.lt_or_ge 123724700094799 n with h12 | h12
            · -- n > 123724700094799
              exact RamareSaouter2003.prime_interval_nat_ladder_c03850 n (by omega) (by omega)
            · -- n <= 123724700094799
              exact RamareSaouter2003.prime_interval_nat_ladder_c03849 n (by omega) (by omega)
          · -- n <= 123419269964407
            rcases Nat.lt_or_ge 123114593827213 n with h12 | h12
            · -- n > 123114593827213
              exact RamareSaouter2003.prime_interval_nat_ladder_c03848 n (by omega) (by omega)
            · -- n <= 123114593827213
              exact RamareSaouter2003.prime_interval_nat_ladder_c03847 n (by omega) (by omega)
        · -- n <= 122810669821589
          rcases Nat.lt_or_ge 122205070783241 n with h10 | h10
          · -- n > 122205070783241
            rcases Nat.lt_or_ge 122507496090961 n with h12 | h12
            · -- n > 122507496090961
              exact RamareSaouter2003.prime_interval_nat_ladder_c03846 n (by omega) (by omega)
            · -- n <= 122507496090961
              exact RamareSaouter2003.prime_interval_nat_ladder_c03845 n (by omega) (by omega)
          · -- n <= 122205070783241
            exact RamareSaouter2003.prime_interval_nat_ladder_c03844 n (by omega) (by omega)
      · -- n <= 121903392050807
        rcases Nat.lt_or_ge 121002816897659 n with h8 | h8
        · -- n > 121002816897659
          rcases Nat.lt_or_ge 121302266944223 n with h10 | h10
          · -- n > 121302266944223
            rcases Nat.lt_or_ge 121602458050609 n with h12 | h12
            · -- n > 121602458050609
              exact RamareSaouter2003.prime_interval_nat_ladder_c03843 n (by omega) (by omega)
            · -- n <= 121602458050609
              exact RamareSaouter2003.prime_interval_nat_ladder_c03842 n (by omega) (by omega)
          · -- n <= 121302266944223
            exact RamareSaouter2003.prime_interval_nat_ladder_c03841 n (by omega) (by omega)
        · -- n <= 121002816897659
          rcases Nat.lt_or_ge 120406132670977 n with h10 | h10
          · -- n > 120406132670977
            rcases Nat.lt_or_ge 120704106081511 n with h12 | h12
            · -- n > 120704106081511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03840 n (by omega) (by omega)
            · -- n <= 120704106081511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03839 n (by omega) (by omega)
          · -- n <= 120406132670977
            exact RamareSaouter2003.prime_interval_nat_ladder_c03838 n (by omega) (by omega)
    · -- n <= 120108894845663
      rcases Nat.lt_or_ge 118340813806337 n with h6 | h6
      · -- n > 118340813806337
        rcases Nat.lt_or_ge 119221576744289 n with h8 | h8
        · -- n > 119221576744289
          rcases Nat.lt_or_ge 119516618691487 n with h10 | h10
          · -- n > 119516618691487
            rcases Nat.lt_or_ge 119812390789633 n with h12 | h12
            · -- n > 119812390789633
              exact RamareSaouter2003.prime_interval_nat_ladder_c03837 n (by omega) (by omega)
            · -- n <= 119812390789633
              exact RamareSaouter2003.prime_interval_nat_ladder_c03836 n (by omega) (by omega)
          · -- n <= 119516618691487
            exact RamareSaouter2003.prime_interval_nat_ladder_c03835 n (by omega) (by omega)
        · -- n <= 119221576744289
          rcases Nat.lt_or_ge 118633676097653 n with h10 | h10
          · -- n > 118633676097653
            rcases Nat.lt_or_ge 118927263145813 n with h12 | h12
            · -- n > 118927263145813
              exact RamareSaouter2003.prime_interval_nat_ladder_c03834 n (by omega) (by omega)
            · -- n <= 118927263145813
              exact RamareSaouter2003.prime_interval_nat_ladder_c03833 n (by omega) (by omega)
          · -- n <= 118633676097653
            exact RamareSaouter2003.prime_interval_nat_ladder_c03832 n (by omega) (by omega)
      · -- n <= 118340813806337
        rcases Nat.lt_or_ge 117466557604547 n with h8 | h8
        · -- n > 117466557604547
          rcases Nat.lt_or_ge 117757256342417 n with h10 | h10
          · -- n > 117757256342417
            rcases Nat.lt_or_ge 118048674482831 n with h12 | h12
            · -- n > 118048674482831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03831 n (by omega) (by omega)
            · -- n <= 118048674482831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03830 n (by omega) (by omega)
          · -- n <= 117757256342417
            exact RamareSaouter2003.prime_interval_nat_ladder_c03829 n (by omega) (by omega)
        · -- n <= 117466557604547
          rcases Nat.lt_or_ge 116887311237601 n with h10 | h10
          · -- n > 116887311237601
            rcases Nat.lt_or_ge 117176576493433 n with h12 | h12
            · -- n > 117176576493433
              exact RamareSaouter2003.prime_interval_nat_ladder_c03828 n (by omega) (by omega)
            · -- n <= 117176576493433
              exact RamareSaouter2003.prime_interval_nat_ladder_c03827 n (by omega) (by omega)
          · -- n <= 116887311237601
            exact RamareSaouter2003.prime_interval_nat_ladder_c03826 n (by omega) (by omega)
  · -- n <= 116598760069697
    rcases Nat.lt_or_ge 112911780722833 n with h4 | h4
    · -- n > 112911780722833
      rcases Nat.lt_or_ge 114598748829157 n with h6 | h6
      · -- n > 114598748829157
        rcases Nat.lt_or_ge 115451661087209 n with h8 | h8
        · -- n > 115451661087209
          rcases Nat.lt_or_ge 116023792951043 n with h10 | h10
          · -- n > 116023792951043
            rcases Nat.lt_or_ge 116310921226957 n with h12 | h12
            · -- n > 116310921226957
              exact RamareSaouter2003.prime_interval_nat_ladder_c03825 n (by omega) (by omega)
            · -- n <= 116310921226957
              exact RamareSaouter2003.prime_interval_nat_ladder_c03824 n (by omega) (by omega)
          · -- n <= 116023792951043
            rcases Nat.lt_or_ge 115737373487737 n with h12 | h12
            · -- n > 115737373487737
              exact RamareSaouter2003.prime_interval_nat_ladder_c03823 n (by omega) (by omega)
            · -- n <= 115737373487737
              exact RamareSaouter2003.prime_interval_nat_ladder_c03822 n (by omega) (by omega)
        · -- n <= 115451661087209
          rcases Nat.lt_or_ge 114882350496917 n with h10 | h10
          · -- n > 114882350496917
            rcases Nat.lt_or_ge 115166654004001 n with h12 | h12
            · -- n > 115166654004001
              exact RamareSaouter2003.prime_interval_nat_ladder_c03821 n (by omega) (by omega)
            · -- n <= 115166654004001
              exact RamareSaouter2003.prime_interval_nat_ladder_c03820 n (by omega) (by omega)
          · -- n <= 114882350496917
            exact RamareSaouter2003.prime_interval_nat_ladder_c03819 n (by omega) (by omega)
      · -- n <= 114598748829157
        rcases Nat.lt_or_ge 113752137557749 n with h8 | h8
        · -- n > 113752137557749
          rcases Nat.lt_or_ge 114033644085733 n with h10 | h10
          · -- n > 114033644085733
            rcases Nat.lt_or_ge 114315847268123 n with h12 | h12
            · -- n > 114315847268123
              exact RamareSaouter2003.prime_interval_nat_ladder_c03818 n (by omega) (by omega)
            · -- n <= 114315847268123
              exact RamareSaouter2003.prime_interval_nat_ladder_c03817 n (by omega) (by omega)
          · -- n <= 114033644085733
            exact RamareSaouter2003.prime_interval_nat_ladder_c03816 n (by omega) (by omega)
        · -- n <= 113752137557749
          rcases Nat.lt_or_ge 113191207589641 n with h10 | h10
          · -- n > 113191207589641
            rcases Nat.lt_or_ge 113471325964141 n with h12 | h12
            · -- n > 113471325964141
              exact RamareSaouter2003.prime_interval_nat_ladder_c03815 n (by omega) (by omega)
            · -- n <= 113471325964141
              exact RamareSaouter2003.prime_interval_nat_ladder_c03814 n (by omega) (by omega)
          · -- n <= 113191207589641
            exact RamareSaouter2003.prime_interval_nat_ladder_c03813 n (by omega) (by omega)
    · -- n <= 112911780722833
      rcases Nat.lt_or_ge 111249645884233 n with h6 | h6
      · -- n > 111249645884233
        rcases Nat.lt_or_ge 112077632119837 n with h8 | h8
        · -- n > 112077632119837
          rcases Nat.lt_or_ge 112354994688941 n with h10 | h10
          · -- n > 112354994688941
            rcases Nat.lt_or_ge 112633043656759 n with h12 | h12
            · -- n > 112633043656759
              exact RamareSaouter2003.prime_interval_nat_ladder_c03812 n (by omega) (by omega)
            · -- n <= 112633043656759
              exact RamareSaouter2003.prime_interval_nat_ladder_c03811 n (by omega) (by omega)
          · -- n <= 112354994688941
            exact RamareSaouter2003.prime_interval_nat_ladder_c03810 n (by omega) (by omega)
        · -- n <= 112077632119837
          rcases Nat.lt_or_ge 111524959405789 n with h10 | h10
          · -- n > 111524959405789
            rcases Nat.lt_or_ge 111800954255537 n with h12 | h12
            · -- n > 111800954255537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03809 n (by omega) (by omega)
            · -- n <= 111800954255537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03808 n (by omega) (by omega)
          · -- n <= 111524959405789
            exact RamareSaouter2003.prime_interval_nat_ladder_c03807 n (by omega) (by omega)
      · -- n <= 111249645884233
        rcases Nat.lt_or_ge 110427776490793 n with h8 | h8
        · -- n > 110427776490793
          rcases Nat.lt_or_ge 110701056102383 n with h10 | h10
          · -- n > 110701056102383
            rcases Nat.lt_or_ge 110975012009021 n with h12 | h12
            · -- n > 110975012009021
              exact RamareSaouter2003.prime_interval_nat_ladder_c03806 n (by omega) (by omega)
            · -- n <= 110975012009021
              exact RamareSaouter2003.prime_interval_nat_ladder_c03805 n (by omega) (by omega)
          · -- n <= 110701056102383
            exact RamareSaouter2003.prime_interval_nat_ladder_c03804 n (by omega) (by omega)
        · -- n <= 110427776490793
          rcases Nat.lt_or_ge 109883239478329 n with h10 | h10
          · -- n > 109883239478329
            rcases Nat.lt_or_ge 110155171504537 n with h12 | h12
            · -- n > 110155171504537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03803 n (by omega) (by omega)
            · -- n <= 110155171504537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03802 n (by omega) (by omega)
          · -- n <= 109883239478329
            exact RamareSaouter2003.prime_interval_nat_ladder_c03801 n (by omega) (by omega)
