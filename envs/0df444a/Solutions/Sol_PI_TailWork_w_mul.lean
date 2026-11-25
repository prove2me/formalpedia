-- Prove2me | solution 1 for PI.TailWork.w_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:35.711045+00:00
-- url     : https://prove2.me/submissions/3d0bed2f-c450-46fd-a4c4-4ad0868d11c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) : (g n - g (n + 1)) * (n : ℝ) = h n - h (n + 1) := by
  unfold g h
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (n : ℝ) ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  push_cast
  simp only [add_sub_cancel_right]
  field_simp
  ring
end PI.TailWork
