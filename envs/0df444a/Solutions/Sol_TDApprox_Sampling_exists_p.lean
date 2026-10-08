-- Prove2me | solution 1 for TDApprox.Sampling.exists_p
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:39:14.540238+00:00
-- url     : https://prove2.me/submissions/4dd8d8f0-c439-4512-a756-18fc24bb92c3

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model
open MeasureTheory
theorem solution
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂) (α : ℝ)
    (hα₁ : (5 : ℝ) / 6 < α) (hα₂ : α < 1) :
    ∃ p : Measure S, ∃ _ : IsProbabilityMeasure p,
      (∀ i, 0 < p {i}) ∧
      5 / (6 * α) < (p {s₂}).toReal ∧
      (p {s₂}).toReal < 1 := by
  classical
  let r : ℝ := 5 / (6 * α)
  have ha : 0 < α := by linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one (by positivity : 0 < 6 * α)]
    linarith
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable'
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0 < 1 - r))) S
  let μ : Measure S := Measure.sum (fun i => δ i • Measure.dirac i)
  have hμ : μ Set.univ = ∑' i, δ i := by simp [μ, Measure.sum_apply]
  have hμi : ∀ i, μ {i} = δ i := fun i => Measure.sum_smul_dirac_singleton
  have hμlt : μ Set.univ < 1 := by
    rw [hμ]
    exact hsum.trans_le (by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (by linarith : 1 - r ≤ 1)))
  let p : Measure S := μ + (1 - μ Set.univ) • Measure.dirac s₂
  have hp : IsProbabilityMeasure p := by
    constructor
    simp only [p, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le hμlt.le
  letI := hp
  have hpos : ∀ i, 0 < p {i} := by
    intro i
    exact (hμi i ▸ hδ i).trans_le (by simp [p, Measure.add_apply])
  refine ⟨p, hp, hpos, ?_, ?_⟩
  · have hl : 1 - μ Set.univ ≤ p {s₂} := by simp [p, Measure.add_apply]
    have hfin : μ Set.univ ≠ ⊤ := ne_top_of_lt hμlt
    have hsmall : (μ Set.univ).toReal < 1 - r := by
      have hsmall' : μ Set.univ < ENNReal.ofReal (1 - r) := by rwa [hμ]
      have htr := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hsmall'
      rwa [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - r)] at htr
    have hlr := ENNReal.toReal_mono (measure_ne_top p {s₂}) hl
    rw [ENNReal.toReal_sub_of_le hμlt.le ENNReal.one_ne_top, ENNReal.toReal_one] at hlr
    dsimp [r] at *
    linarith
  · have hu : p {s₁} + p {s₂} ≤ 1 := by
      rw [← measure_union (by simp [Set.disjoint_singleton, hne]) (measurableSet_singleton s₂)]
      exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : p Set.univ = 1)
    have hur := ENNReal.toReal_mono ENNReal.one_ne_top hu
    rw [ENNReal.toReal_add (measure_ne_top p _) (measure_ne_top p _), ENNReal.toReal_one] at hur
    have h1 := ENNReal.toReal_pos (ne_of_gt (hpos s₁)) (measure_ne_top p {s₁})
    linarith
#print axioms solution
