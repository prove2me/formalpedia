-- Prove2me | solution 1 for PI.EF.sum_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:27.042142+00:00
-- url     : https://prove2.me/submissions/46bee736-52fb-4270-ae15-400096a0914a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ range n, 1 / ((j : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    simp [one_div]
  rw [← e]
  exact h
end PI.EF
