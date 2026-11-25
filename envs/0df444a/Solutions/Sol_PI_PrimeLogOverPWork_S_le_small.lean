-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:07.104956+00:00
-- url     : https://prove2.me/submissions/678af6be-4ea2-42bf-8b65-ac540aef7cd2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_1_1
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_2_2
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_3_4
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_5_10
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_11_30
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_31_63
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_of_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset
namespace PI.PrimeLogOverPWork
theorem _root_.solution (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 63) : S n ≤ Real.log (n : ℝ) := by
  by_cases hA : n ≤ 1
  · exact S_le_of_block (a := 1) (b := 1) (by norm_num)
      (by exact_mod_cast S_le_1_1) h1 hA
  by_cases hB : n ≤ 2
  · exact S_le_of_block (a := 2) (b := 2) (by norm_num)
      (by exact_mod_cast S_le_2_2) (by omega) hB
  by_cases hC : n ≤ 4
  · exact S_le_of_block (a := 3) (b := 4) (by norm_num)
      (by exact_mod_cast S_le_3_4) (by omega) hC
  by_cases hD : n ≤ 10
  · exact S_le_of_block (a := 5) (b := 10) (by norm_num)
      (by exact_mod_cast S_le_5_10) (by omega) hD
  by_cases hE : n ≤ 30
  · exact S_le_of_block (a := 11) (b := 30) (by norm_num)
      (by exact_mod_cast S_le_11_30) (by omega) hE
  exact S_le_of_block (a := 31) (b := 63) (by norm_num)
    (by exact_mod_cast S_le_31_63) (by omega) h2
end PI.PrimeLogOverPWork
