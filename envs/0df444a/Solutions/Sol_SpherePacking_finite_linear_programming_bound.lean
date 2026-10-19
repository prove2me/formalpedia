-- Prove2me | solution 1 for SpherePacking.finite_linear_programming_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/55881ea9-d6d8-494d-a371-b95a3f8d8771

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
theorem _root_.solution {α : Type*}
    (C : Finset α) (f : α → α → ℝ) {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hdiag : ∀ x ∈ C, f x x ≤ B)
    (hoff : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → f x y ≤ 0)
    (hpositive : (C.card : ℝ) ^ 2 * c ≤
      ∑ x ∈ C, ∑ y ∈ C, f x y) :
    (C.card : ℝ) ≤ B / c := by
  classical
  have hsum :
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤ (C.card : ℝ) * B := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
          ∑ x ∈ C, ∑ y ∈ C, if x = y then B else 0 := by
            exact Finset.sum_le_sum fun x hx =>
              Finset.sum_le_sum fun y hy => by
                split_ifs with hxy
                · subst y
                  exact hdiag x hx
                · exact hoff x hx y hy hxy
      _ = (C.card : ℝ) * B := by
        simp
  by_cases hC : C.card = 0
  · rw [hC]
    norm_num
    exact div_nonneg hB hc.le
  · have hcard : 0 < (C.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hC
    apply (le_div_iff₀ hc).2
    nlinarith [hpositive, hsum]
end SpherePacking
