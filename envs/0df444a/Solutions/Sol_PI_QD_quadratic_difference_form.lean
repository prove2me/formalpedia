-- Prove2me | solution 1 for PI.QD.quadratic_difference_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:28.610856+00:00
-- url     : https://prove2.me/submissions/bd479c28-317b-4b66-88f6-ef7b3edfbe56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuadDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadDiffOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.QD
open NumberField Polynomial
namespace PI.QD
theorem _root_.solution : Form := by
  intro K _ _ d θ hθ htop z
  have hz : z ∈ Algebra.adjoin ℚ {θ} := by rw [htop]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    exact ⟨0, 1, by rw [hw]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    exact ⟨x1 + x2, y1 + y2, by rw [e1, e2]; push_cast; ring⟩
  | mul w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    refine ⟨x1 * x2 - d * y1 * y2, x1 * y2 + x2 * y1, ?_⟩
    rw [e1, e2]; push_cast
    linear_combination (y1 * y2 : K) * hθ
end PI.QD
