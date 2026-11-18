-- Prove2me | solution 1 for OWMR.renewal_doubling
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:05.588694+00:00
-- url     : https://prove2.me/submissions/6665b57f-2141-4718-9843-98cb1d6e1523

import Theorems.Thm_OWMR_renewal_interval_bound

/-!
Lemma 2, doubling bound `M(2w) ≤ 2 M(w)`, from the interval bound `U[w, 2w) ≤ M(w)` of the same
lemma and the partition `[0, 2w) = [0, w) ∪ [w, 2w)`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 ≤ w) :
    renewalMeasure ρ (Set.Ico 0 (2 * w)) ≤ 2 * renewalMeasure ρ (Set.Ico 0 w) := by
  have hsplit : Set.Ico (0 : ℝ) (2 * w) = Set.Ico 0 w ∪ Set.Ico w (w + w) := by
    rw [Set.Ico_union_Ico_eq_Ico hw (by linarith), two_mul]
  rw [hsplit, two_mul]
  exact (measure_union_le _ _).trans (add_le_add le_rfl (renewal_interval_bound ρ w w hw))
