-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T18:55:57.458334+00:00
-- url     : https://prove2.me/submissions/42ebb74b-66e4-4a74-a38a-8c530839d573

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05850

theorem solution (n : Nat)
    (hn : 29870561433150253 < n) (hupper : n <= 34405922531916673) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 32058098977593431 n with h2 | h2
  · -- n > 32058098977593431
    rcases Nat.lt_or_ge 33164367058575397 n with h4 | h4
    · -- n > 33164367058575397
      rcases Nat.lt_or_ge 33731734106410013 n with h6 | h6
      · -- n > 33731734106410013
        rcases Nat.lt_or_ge 34019041136847017 n with h8 | h8
        · -- n > 34019041136847017
          rcases Nat.lt_or_ge 34211938536401503 n with h10 | h10
          · -- n > 34211938536401503
            rcases Nat.lt_or_ge 34308790490395439 n with h12 | h12
            · -- n > 34308790490395439
              exact RamareSaouter2003.prime_interval_nat_ladder_c05850 n (by omega) (by omega)
            · -- n <= 34308790490395439
              exact RamareSaouter2003.prime_interval_nat_ladder_c05849 n (by omega) (by omega)
          · -- n <= 34211938536401503
            rcases Nat.lt_or_ge 34115358321449737 n with h12 | h12
            · -- n > 34115358321449737
              exact RamareSaouter2003.prime_interval_nat_ladder_c05848 n (by omega) (by omega)
            · -- n <= 34115358321449737
              exact RamareSaouter2003.prime_interval_nat_ladder_c05847 n (by omega) (by omega)
        · -- n <= 34019041136847017
          rcases Nat.lt_or_ge 33827236801828321 n with h10 | h10
          · -- n > 33827236801828321
            rcases Nat.lt_or_ge 33923004883393303 n with h12 | h12
            · -- n > 33923004883393303
              exact RamareSaouter2003.prime_interval_nat_ladder_c05846 n (by omega) (by omega)
            · -- n <= 33923004883393303
              exact RamareSaouter2003.prime_interval_nat_ladder_c05845 n (by omega) (by omega)
          · -- n <= 33827236801828321
            exact RamareSaouter2003.prime_interval_nat_ladder_c05844 n (by omega) (by omega)
      · -- n <= 33731734106410013
        rcases Nat.lt_or_ge 33446851404033047 n with h8 | h8
        · -- n > 33446851404033047
          rcases Nat.lt_or_ge 33541544746050703 n with h10 | h10
          · -- n > 33541544746050703
            rcases Nat.lt_or_ge 33636503991759157 n with h12 | h12
            · -- n > 33636503991759157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05843 n (by omega) (by omega)
            · -- n <= 33636503991759157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05842 n (by omega) (by omega)
          · -- n <= 33541544746050703
            exact RamareSaouter2003.prime_interval_nat_ladder_c05841 n (by omega) (by omega)
        · -- n <= 33446851404033047
          rcases Nat.lt_or_ge 33258262760598163 n with h10 | h10
          · -- n > 33258262760598163
            rcases Nat.lt_or_ge 33352422316816157 n with h12 | h12
            · -- n > 33352422316816157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05840 n (by omega) (by omega)
            · -- n <= 33352422316816157
              exact RamareSaouter2003.prime_interval_nat_ladder_c05839 n (by omega) (by omega)
          · -- n <= 33258262760598163
            exact RamareSaouter2003.prime_interval_nat_ladder_c05838 n (by omega) (by omega)
    · -- n <= 33164367058575397
      rcases Nat.lt_or_ge 32606549068707017 n with h6 | h6
      · -- n > 32606549068707017
        rcases Nat.lt_or_ge 32884266984811009 n with h8 | h8
        · -- n > 32884266984811009
          rcases Nat.lt_or_ge 32977367917672609 n with h10 | h10
          · -- n > 32977367917672609
            rcases Nat.lt_or_ge 33070735748978353 n with h12 | h12
            · -- n > 33070735748978353
              exact RamareSaouter2003.prime_interval_nat_ladder_c05837 n (by omega) (by omega)
            · -- n <= 33070735748978353
              exact RamareSaouter2003.prime_interval_nat_ladder_c05836 n (by omega) (by omega)
          · -- n <= 32977367917672609
            exact RamareSaouter2003.prime_interval_nat_ladder_c05835 n (by omega) (by omega)
        · -- n <= 32884266984811009
          rcases Nat.lt_or_ge 32698862475071459 n with h10 | h10
          · -- n > 32698862475071459
            rcases Nat.lt_or_ge 32791428407236319 n with h12 | h12
            · -- n > 32791428407236319
              exact RamareSaouter2003.prime_interval_nat_ladder_c05834 n (by omega) (by omega)
            · -- n <= 32791428407236319
              exact RamareSaouter2003.prime_interval_nat_ladder_c05833 n (by omega) (by omega)
          · -- n <= 32698862475071459
            exact RamareSaouter2003.prime_interval_nat_ladder_c05832 n (by omega) (by omega)
      · -- n <= 32606549068707017
        rcases Nat.lt_or_ge 32331159971646593 n with h8 | h8
        · -- n > 32331159971646593
          rcases Nat.lt_or_ge 32422697297670499 n with h10 | h10
          · -- n > 32422697297670499
            rcases Nat.lt_or_ge 32514491666667319 n with h12 | h12
            · -- n > 32514491666667319
              exact RamareSaouter2003.prime_interval_nat_ladder_c05831 n (by omega) (by omega)
            · -- n <= 32514491666667319
              exact RamareSaouter2003.prime_interval_nat_ladder_c05830 n (by omega) (by omega)
          · -- n <= 32422697297670499
            exact RamareSaouter2003.prime_interval_nat_ladder_c05829 n (by omega) (by omega)
        · -- n <= 32331159971646593
          rcases Nat.lt_or_ge 32148864414052367 n with h10 | h10
          · -- n > 32148864414052367
            rcases Nat.lt_or_ge 32239881694683233 n with h12 | h12
            · -- n > 32239881694683233
              exact RamareSaouter2003.prime_interval_nat_ladder_c05828 n (by omega) (by omega)
            · -- n <= 32239881694683233
              exact RamareSaouter2003.prime_interval_nat_ladder_c05827 n (by omega) (by omega)
          · -- n <= 32148864414052367
            exact RamareSaouter2003.prime_interval_nat_ladder_c05826 n (by omega) (by omega)
  · -- n <= 32058098977593431
    rcases Nat.lt_or_ge 30901336400127533 n with h4 | h4
    · -- n > 30901336400127533
      rcases Nat.lt_or_ge 31429967440274903 n with h6 | h6
      · -- n > 31429967440274903
        rcases Nat.lt_or_ge 31697618896059797 n with h8 | h8
        · -- n > 31697618896059797
          rcases Nat.lt_or_ge 31877338314538687 n with h10 | h10
          · -- n > 31877338314538687
            rcases Nat.lt_or_ge 31967589136428773 n with h12 | h12
            · -- n > 31967589136428773
              exact RamareSaouter2003.prime_interval_nat_ladder_c05825 n (by omega) (by omega)
            · -- n <= 31967589136428773
              exact RamareSaouter2003.prime_interval_nat_ladder_c05824 n (by omega) (by omega)
          · -- n <= 31877338314538687
            rcases Nat.lt_or_ge 31787351627806799 n with h12 | h12
            · -- n > 31787351627806799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05823 n (by omega) (by omega)
            · -- n <= 31787351627806799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05822 n (by omega) (by omega)
        · -- n <= 31697618896059797
          rcases Nat.lt_or_ge 31518948313853503 n with h10 | h10
          · -- n > 31518948313853503
            rcases Nat.lt_or_ge 31608157720101101 n with h12 | h12
            · -- n > 31608157720101101
              exact RamareSaouter2003.prime_interval_nat_ladder_c05821 n (by omega) (by omega)
            · -- n <= 31608157720101101
              exact RamareSaouter2003.prime_interval_nat_ladder_c05820 n (by omega) (by omega)
          · -- n <= 31518948313853503
            exact RamareSaouter2003.prime_interval_nat_ladder_c05819 n (by omega) (by omega)
      · -- n <= 31429967440274903
        rcases Nat.lt_or_ge 31164527636997089 n with h8 | h8
        · -- n > 31164527636997089
          rcases Nat.lt_or_ge 31252757107512469 n with h10 | h10
          · -- n > 31252757107512469
            rcases Nat.lt_or_ge 31341241233363697 n with h12 | h12
            · -- n > 31341241233363697
              exact RamareSaouter2003.prime_interval_nat_ladder_c05818 n (by omega) (by omega)
            · -- n <= 31341241233363697
              exact RamareSaouter2003.prime_interval_nat_ladder_c05817 n (by omega) (by omega)
          · -- n <= 31252757107512469
            exact RamareSaouter2003.prime_interval_nat_ladder_c05816 n (by omega) (by omega)
        · -- n <= 31164527636997089
          rcases Nat.lt_or_ge 30988818877169479 n with h10 | h10
          · -- n > 30988818877169479
            rcases Nat.lt_or_ge 31076548060152253 n with h12 | h12
            · -- n > 31076548060152253
              exact RamareSaouter2003.prime_interval_nat_ladder_c05815 n (by omega) (by omega)
            · -- n <= 31076548060152253
              exact RamareSaouter2003.prime_interval_nat_ladder_c05814 n (by omega) (by omega)
          · -- n <= 30988818877169479
            exact RamareSaouter2003.prime_interval_nat_ladder_c05813 n (by omega) (by omega)
    · -- n <= 30901336400127533
      rcases Nat.lt_or_ge 30381589051841341 n with h6 | h6
      · -- n > 30381589051841341
        rcases Nat.lt_or_ge 30640352088997151 n with h8 | h8
        · -- n > 30640352088997151
          rcases Nat.lt_or_ge 30727098257234263 n with h10 | h10
          · -- n > 30727098257234263
            rcases Nat.lt_or_ge 30814095894339301 n with h12 | h12
            · -- n > 30814095894339301
              exact RamareSaouter2003.prime_interval_nat_ladder_c05812 n (by omega) (by omega)
            · -- n <= 30814095894339301
              exact RamareSaouter2003.prime_interval_nat_ladder_c05811 n (by omega) (by omega)
          · -- n <= 30727098257234263
            exact RamareSaouter2003.prime_interval_nat_ladder_c05810 n (by omega) (by omega)
        · -- n <= 30640352088997151
          rcases Nat.lt_or_ge 30467597307345889 n with h10 | h10
          · -- n > 30467597307345889
            rcases Nat.lt_or_ge 30553850547507799 n with h12 | h12
            · -- n > 30553850547507799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05809 n (by omega) (by omega)
            · -- n <= 30553850547507799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05808 n (by omega) (by omega)
          · -- n <= 30467597307345889
            exact RamareSaouter2003.prime_interval_nat_ladder_c05807 n (by omega) (by omega)
      · -- n <= 30381589051841341
        rcases Nat.lt_or_ge 30124990364974643 n with h8 | h8
        · -- n > 30124990364974643
          rcases Nat.lt_or_ge 30210279282694103 n with h10 | h10
          · -- n > 30210279282694103
            rcases Nat.lt_or_ge 30295812708920929 n with h12 | h12
            · -- n > 30295812708920929
              exact RamareSaouter2003.prime_interval_nat_ladder_c05806 n (by omega) (by omega)
            · -- n <= 30295812708920929
              exact RamareSaouter2003.prime_interval_nat_ladder_c05805 n (by omega) (by omega)
          · -- n <= 30210279282694103
            exact RamareSaouter2003.prime_interval_nat_ladder_c05804 n (by omega) (by omega)
        · -- n <= 30124990364974643
          rcases Nat.lt_or_ge 29955128991772367 n with h10 | h10
          · -- n > 29955128991772367
            rcases Nat.lt_or_ge 30039939162605971 n with h12 | h12
            · -- n > 30039939162605971
              exact RamareSaouter2003.prime_interval_nat_ladder_c05803 n (by omega) (by omega)
            · -- n <= 30039939162605971
              exact RamareSaouter2003.prime_interval_nat_ladder_c05802 n (by omega) (by omega)
          · -- n <= 29955128991772367
            exact RamareSaouter2003.prime_interval_nat_ladder_c05801 n (by omega) (by omega)
