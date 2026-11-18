-- Prove2me | solution 1 for OWMR.renewal_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T03:07:33.399723+00:00
-- url     : https://prove2.me/submissions/c3b15fdf-435c-401f-a8af-9fe81e1075d1

import Theorems.Thm_OWMR_renewal_regeneration

/-!
Lemma 2, interval bound `U[x, x+w) ≤ M(w)` for `x ≥ 0`: apply the regeneration inequality at the
level `c = x` to the indicator of `[x, x+w)`. A fresh partial-sum process started at `y ≥ x` meets
`[x, x+w)` only at depletions in `[x-y, x+w-y) ⊆ (-∞, 0) ∪ [0, w)`, and `U` puts no mass on `(-∞, 0)`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- Partial sums of nonnegative demands are nonnegative: `U(-∞, 0) = 0`. -/
private lemma renewal_Iio_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    renewalMeasure ρ (Set.Iio 0) = 0 := by
  unfold renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Iio]
  have : (fun z : Fin n → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Iio 0 = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Finset.sum_nonneg fun j _ => (z j).2
  rw [this, measure_empty]

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (x w : ℝ) (hx : 0 ≤ x) :
    renewalMeasure ρ (Set.Ico x (x + w)) ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  have h := renewal_regeneration ρ x ((Set.Ico x (x + w)).indicator 1)
    (measurable_one.indicator measurableSet_Ico)
  have hl : ∫⁻ t in Set.Ici x, (Set.Ico x (x + w)).indicator 1 t ∂renewalMeasure ρ
      = renewalMeasure ρ (Set.Ico x (x + w)) := by
    rw [lintegral_indicator_one measurableSet_Ico, Measure.restrict_apply measurableSet_Ico,
      Set.inter_eq_left.2 Set.Ico_subset_Ici_self]
  rw [hl] at h
  refine h.trans (iSup₂_le fun y hy => ?_)
  have hsub : (fun t => y + t) ⁻¹' Set.Ico x (x + w) ⊆ Set.Iio 0 ∪ Set.Ico 0 w := by
    intro t ht
    simp only [Set.mem_preimage, Set.mem_Ico] at ht
    by_cases h0 : t < 0
    · exact Or.inl h0
    · exact Or.inr ⟨not_lt.1 h0, by linarith [Set.mem_Ici.1 hy]⟩
  calc ∫⁻ t, (Set.Ico x (x + w)).indicator 1 (y + t) ∂renewalMeasure ρ
      = ∫⁻ t, ((fun t => y + t) ⁻¹' Set.Ico x (x + w)).indicator 1 t ∂renewalMeasure ρ := rfl
    _ = renewalMeasure ρ ((fun t => y + t) ⁻¹' Set.Ico x (x + w)) :=
        lintegral_indicator_one (measurableSet_Ico.preimage (measurable_const_add y))
    _ ≤ renewalMeasure ρ (Set.Iio 0 ∪ Set.Ico 0 w) := measure_mono hsub
    _ ≤ renewalMeasure ρ (Set.Iio 0) + renewalMeasure ρ (Set.Ico 0 w) := measure_union_le _ _
    _ = renewalMeasure ρ (Set.Ico 0 w) := by rw [renewal_Iio_zero, zero_add]
