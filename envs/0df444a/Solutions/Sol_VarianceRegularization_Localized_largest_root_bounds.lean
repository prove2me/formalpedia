-- Prove2me | solution 1 for VarianceRegularization.Localized.largest_root_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:37:39.559136+00:00
-- url     : https://prove2.me/submissions/6118e22c-8fa0-41ef-b7d4-c03be0bb3b1a

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

open VarianceRegularization.Localized in
theorem solution (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hx : 0 ≤ x)
    (heq : a * x + b = x ^ 2 / d) :
    a ^ 2 * d ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ a ^ 2 * d ^ 2 + 2 * b * d := by
  have h2 : x ^ 2 = a * d * x + b * d := by
    field_simp at heq; linarith
  have had : 0 < a * d := mul_pos ha hd
  have hbd : 0 < b * d := mul_pos hb hd
  have hxge : a * d ≤ x := by
    by_contra h
    push_neg at h
    nlinarith
  refine ⟨by nlinarith, ?_⟩
  -- need a d x ≤ a^2 d^2 + b d
  have key : a * d * x ≤ a ^ 2 * d ^ 2 + b * d := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (x - a * d)]
  nlinarith
