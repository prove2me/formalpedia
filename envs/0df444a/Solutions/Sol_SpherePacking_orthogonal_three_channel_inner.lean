-- Prove2me | solution 1 for SpherePacking.orthogonal_three_channel_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/9b07ce72-ad0d-4a85-adb2-162e5e69b692

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
    (p m r : α → E) (a b : ℝ)
    (hpm : ∀ x y, ⟪p x, m y⟫_ℝ = 0)
    (hpr : ∀ x y, ⟪p x, r y⟫_ℝ = 0)
    (hmr : ∀ x y, ⟪m x, r y⟫_ℝ = 0)
    (x y : α) :
    ⟪a • p x + b • m x + r x,
      a • p y + b • m y + r y⟫_ℝ =
      a ^ 2 * ⟪p x, p y⟫_ℝ +
        b ^ 2 * ⟪m x, m y⟫_ℝ + ⟪r x, r y⟫_ℝ := by
  have hmp : ⟪m x, p y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpm y x
  have hrp : ⟪r x, p y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpr y x
  have hrm : ⟪r x, m y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hmr y x
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    hpm x y, hpr x y, hmr x y, hmp, hrp, hrm,
    mul_zero, add_zero, zero_add]
  ring
end SpherePacking
