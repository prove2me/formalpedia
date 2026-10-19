-- Prove2me | solution 1 for SpherePacking.weighted_gram_sum_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/3f84df59-c32a-46de-919e-650a48e4f030

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Finset α) (w : α → ℝ) (v : α → E) :
    (∑ x ∈ C, ∑ y ∈ C, w x * w y * ⟪v x, v y⟫_ℝ) =
      ‖∑ x ∈ C, w x • v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [real_inner_comm (v x) (v y), mul_assoc]
end SpherePacking
