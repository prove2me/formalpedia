-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T01:49:32.941196+00:00
-- url     : https://prove2.me/submissions/e53de845-4ee6-4735-a3bc-a31e27cd0a3f

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06850

theorem solution (n : Nat)
    (hn : 504749525047989457 < n) (hupper : n <= 581391753836179799) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 541717085942114353 n with h2 | h2
  · -- n > 541717085942114353
    rcases Nat.lt_or_ge 560411142346516151 n with h4 | h4
    · -- n > 560411142346516151
      rcases Nat.lt_or_ge 569998699399061873 n with h6 | h6
      · -- n > 569998699399061873
        rcases Nat.lt_or_ge 574853752936401559 n with h8 | h8
        · -- n > 574853752936401559
          rcases Nat.lt_or_ge 578113516096686979 n with h10 | h10
          · -- n > 578113516096686979
            rcases Nat.lt_or_ge 579750332817024143 n with h12 | h12
            · -- n > 579750332817024143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06850 n (by omega) (by omega)
            · -- n <= 579750332817024143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06849 n (by omega) (by omega)
          · -- n <= 578113516096686979
            rcases Nat.lt_or_ge 576481330687979683 n with h12 | h12
            · -- n > 576481330687979683
              exact RamareSaouter2003.prime_interval_nat_ladder_c06848 n (by omega) (by omega)
            · -- n <= 576481330687979683
              exact RamareSaouter2003.prime_interval_nat_ladder_c06847 n (by omega) (by omega)
        · -- n <= 574853752936401559
          rcases Nat.lt_or_ge 571612508335310437 n with h10 | h10
          · -- n > 571612508335310437
            rcases Nat.lt_or_ge 573230776014145313 n with h12 | h12
            · -- n > 573230776014145313
              exact RamareSaouter2003.prime_interval_nat_ladder_c06846 n (by omega) (by omega)
            · -- n <= 573230776014145313
              exact RamareSaouter2003.prime_interval_nat_ladder_c06845 n (by omega) (by omega)
          · -- n <= 571612508335310437
            exact RamareSaouter2003.prime_interval_nat_ladder_c06844 n (by omega) (by omega)
      · -- n <= 569998699399061873
        rcases Nat.lt_or_ge 565184513738336399 n with h8 | h8
        · -- n > 565184513738336399
          rcases Nat.lt_or_ge 566784692145337181 n with h10 | h10
          · -- n > 566784692145337181
            rcases Nat.lt_or_ge 568389427558094309 n with h12 | h12
            · -- n > 568389427558094309
              exact RamareSaouter2003.prime_interval_nat_ladder_c06843 n (by omega) (by omega)
            · -- n <= 568389427558094309
              exact RamareSaouter2003.prime_interval_nat_ladder_c06842 n (by omega) (by omega)
          · -- n <= 566784692145337181
            exact RamareSaouter2003.prime_interval_nat_ladder_c06841 n (by omega) (by omega)
        · -- n <= 565184513738336399
          rcases Nat.lt_or_ge 561997734933748709 n with h10 | h10
          · -- n > 561997734933748709
            rcases Nat.lt_or_ge 563588828473782263 n with h12 | h12
            · -- n > 563588828473782263
              exact RamareSaouter2003.prime_interval_nat_ladder_c06840 n (by omega) (by omega)
            · -- n <= 563588828473782263
              exact RamareSaouter2003.prime_interval_nat_ladder_c06839 n (by omega) (by omega)
          · -- n <= 561997734933748709
            exact RamareSaouter2003.prime_interval_nat_ladder_c06838 n (by omega) (by omega)
    · -- n <= 560411142346516151
      rcases Nat.lt_or_ge 550984981137010837 n with h6 | h6
      · -- n > 550984981137010837
        rcases Nat.lt_or_ge 555677971832179769 n with h8 | h8
        · -- n > 555677971832179769
          rcases Nat.lt_or_ge 557251264874913359 n with h10 | h10
          · -- n > 557251264874913359
            rcases Nat.lt_or_ge 558828967859616967 n with h12 | h12
            · -- n > 558828967859616967
              exact RamareSaouter2003.prime_interval_nat_ladder_c06837 n (by omega) (by omega)
            · -- n <= 558828967859616967
              exact RamareSaouter2003.prime_interval_nat_ladder_c06836 n (by omega) (by omega)
          · -- n <= 557251264874913359
            exact RamareSaouter2003.prime_interval_nat_ladder_c06835 n (by omega) (by omega)
        · -- n <= 555677971832179769
          rcases Nat.lt_or_ge 552544917674506591 n with h10 | h10
          · -- n > 552544917674506591
            rcases Nat.lt_or_ge 554109291012874801 n with h12 | h12
            · -- n > 554109291012874801
              exact RamareSaouter2003.prime_interval_nat_ladder_c06834 n (by omega) (by omega)
            · -- n <= 554109291012874801
              exact RamareSaouter2003.prime_interval_nat_ladder_c06833 n (by omega) (by omega)
          · -- n <= 552544917674506591
            exact RamareSaouter2003.prime_interval_nat_ladder_c06832 n (by omega) (by omega)
      · -- n <= 550984981137010837
        rcases Nat.lt_or_ge 546331367909724181 n with h8 | h8
        · -- n > 546331367909724181
          rcases Nat.lt_or_ge 547878199924372063 n with h10 | h10
          · -- n > 547878199924372063
            rcases Nat.lt_or_ge 549429382894014737 n with h12 | h12
            · -- n > 549429382894014737
              exact RamareSaouter2003.prime_interval_nat_ladder_c06831 n (by omega) (by omega)
            · -- n <= 549429382894014737
              exact RamareSaouter2003.prime_interval_nat_ladder_c06830 n (by omega) (by omega)
          · -- n <= 547878199924372063
            exact RamareSaouter2003.prime_interval_nat_ladder_c06829 n (by omega) (by omega)
        · -- n <= 546331367909724181
          rcases Nat.lt_or_ge 543250826947293193 n with h10 | h10
          · -- n > 543250826947293193
            rcases Nat.lt_or_ge 544788916387855417 n with h12 | h12
            · -- n > 544788916387855417
              exact RamareSaouter2003.prime_interval_nat_ladder_c06828 n (by omega) (by omega)
            · -- n <= 544788916387855417
              exact RamareSaouter2003.prime_interval_nat_ladder_c06827 n (by omega) (by omega)
          · -- n <= 543250826947293193
            exact RamareSaouter2003.prime_interval_nat_ladder_c06826 n (by omega) (by omega)
  · -- n <= 541717085942114353
    rcases Nat.lt_or_ge 522168026299383017 n with h4 | h4
    · -- n > 522168026299383017
      rcases Nat.lt_or_ge 531101498307770119 n with h6 | h6
      · -- n > 531101498307770119
        rcases Nat.lt_or_ge 535625334704259043 n with h8 | h8
        · -- n > 535625334704259043
          rcases Nat.lt_or_ge 538662647776674767 n with h10 | h10
          · -- n > 538662647776674767
            rcases Nat.lt_or_ge 540187746002411341 n with h12 | h12
            · -- n > 540187746002411341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06825 n (by omega) (by omega)
            · -- n <= 540187746002411341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06824 n (by omega) (by omega)
          · -- n <= 538662647776674767
            rcases Nat.lt_or_ge 537141854425573307 n with h12 | h12
            · -- n > 537141854425573307
              exact RamareSaouter2003.prime_interval_nat_ladder_c06823 n (by omega) (by omega)
            · -- n <= 537141854425573307
              exact RamareSaouter2003.prime_interval_nat_ladder_c06822 n (by omega) (by omega)
        · -- n <= 535625334704259043
          rcases Nat.lt_or_ge 532605181161937277 n with h10 | h10
          · -- n > 532605181161937277
            rcases Nat.lt_or_ge 534113113246145333 n with h12 | h12
            · -- n > 534113113246145333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06821 n (by omega) (by omega)
            · -- n <= 534113113246145333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06820 n (by omega) (by omega)
          · -- n <= 532605181161937277
            exact RamareSaouter2003.prime_interval_nat_ladder_c06819 n (by omega) (by omega)
      · -- n <= 531101498307770119
        rcases Nat.lt_or_ge 526615814842591601 n with h8 | h8
        · -- n > 526615814842591601
          rcases Nat.lt_or_ge 528106813279256929 n with h10 | h10
          · -- n > 528106813279256929
            rcases Nat.lt_or_ge 529602038606566787 n with h12 | h12
            · -- n > 529602038606566787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06818 n (by omega) (by omega)
            · -- n <= 529602038606566787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06817 n (by omega) (by omega)
          · -- n <= 528106813279256929
            exact RamareSaouter2003.prime_interval_nat_ladder_c06816 n (by omega) (by omega)
        · -- n <= 526615814842591601
          rcases Nat.lt_or_ge 523646433864902459 n with h10 | h10
          · -- n > 523646433864902459
            rcases Nat.lt_or_ge 525129018399715363 n with h12 | h12
            · -- n > 525129018399715363
              exact RamareSaouter2003.prime_interval_nat_ladder_c06815 n (by omega) (by omega)
            · -- n <= 525129018399715363
              exact RamareSaouter2003.prime_interval_nat_ladder_c06814 n (by omega) (by omega)
          · -- n <= 523646433864902459
            exact RamareSaouter2003.prime_interval_nat_ladder_c06813 n (by omega) (by omega)
    · -- n <= 522168026299383017
      rcases Nat.lt_or_ge 513384870444586841 n with h6 | h6
      · -- n > 513384870444586841
        rcases Nat.lt_or_ge 517757836053573889 n with h8 | h8
        · -- n > 517757836053573889
          rcases Nat.lt_or_ge 519223754210268439 n with h10 | h10
          · -- n > 519223754210268439
            rcases Nat.lt_or_ge 520693828689344143 n with h12 | h12
            · -- n > 520693828689344143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06812 n (by omega) (by omega)
            · -- n <= 520693828689344143
              exact RamareSaouter2003.prime_interval_nat_ladder_c06811 n (by omega) (by omega)
          · -- n <= 519223754210268439
            exact RamareSaouter2003.prime_interval_nat_ladder_c06810 n (by omega) (by omega)
        · -- n <= 517757836053573889
          rcases Nat.lt_or_ge 514838401506273989 n with h10 | h10
          · -- n > 514838401506273989
            rcases Nat.lt_or_ge 516296047998219947 n with h12 | h12
            · -- n > 516296047998219947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06809 n (by omega) (by omega)
            · -- n <= 516296047998219947
              exact RamareSaouter2003.prime_interval_nat_ladder_c06808 n (by omega) (by omega)
          · -- n <= 514838401506273989
            exact RamareSaouter2003.prime_interval_nat_ladder_c06807 n (by omega) (by omega)
      · -- n <= 513384870444586841
        rcases Nat.lt_or_ge 509048857863303761 n with h8 | h8
        · -- n > 509048857863303761
          rcases Nat.lt_or_ge 510490111678116083 n with h10 | h10
          · -- n > 510490111678116083
            rcases Nat.lt_or_ge 511935446325754537 n with h12 | h12
            · -- n > 511935446325754537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06806 n (by omega) (by omega)
            · -- n <= 511935446325754537
              exact RamareSaouter2003.prime_interval_nat_ladder_c06805 n (by omega) (by omega)
          · -- n <= 510490111678116083
            exact RamareSaouter2003.prime_interval_nat_ladder_c06804 n (by omega) (by omega)
        · -- n <= 509048857863303761
          rcases Nat.lt_or_ge 506178541172651681 n with h10 | h10
          · -- n > 506178541172651681
            rcases Nat.lt_or_ge 507611676296360123 n with h12 | h12
            · -- n > 507611676296360123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06803 n (by omega) (by omega)
            · -- n <= 507611676296360123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06802 n (by omega) (by omega)
          · -- n <= 506178541172651681
            exact RamareSaouter2003.prime_interval_nat_ladder_c06801 n (by omega) (by omega)
