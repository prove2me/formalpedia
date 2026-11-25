-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_of_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:11.2602+00:00
-- url     : https://prove2.me/submissions/5c445bfe-5297-47ff-b13f-c97dad8d6988

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_S_mono


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
theorem _root_.solution {a b n : ℕ} (ha : 0 < a) (h : S b ≤ Real.log (a : ℝ)) (h1 : a ≤ n)
    (h2 : n ≤ b) : S n ≤ Real.log (n : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1' : (a : ℝ) ≤ n := by exact_mod_cast h1
  calc S n ≤ S b := S_mono h2
    _ ≤ Real.log (a : ℝ) := h
    _ ≤ Real.log (n : ℝ) := Real.log_le_log ha' h1'
end PI.PrimeLogOverPWork
