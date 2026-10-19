-- Prove2me | solution 1 for SpherePacking.weighted_gram_sum_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/ee2a3663-ba63-4007-9d75-71de2f0154be

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_weighted_gram_sum_eq_norm_sq

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
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, w x * w y * ⟪v x, v y⟫_ℝ := by
  rw [weighted_gram_sum_eq_norm_sq]
  exact sq_nonneg _
end SpherePacking
