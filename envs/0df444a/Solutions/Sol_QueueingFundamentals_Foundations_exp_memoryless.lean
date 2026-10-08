-- Prove2me | solution 1 for QueueingFundamentals.Foundations.exp_memoryless
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:45:35.376984+00:00
-- url     : https://prove2.me/submissions/1a9087a6-e430-4254-b1a8-3770ddc6199c

import Mathlib

open MeasureTheory ProbabilityTheory


namespace QueueingFundamentals.Foundations

open Set

lemma qfb_exp_noatoms (lam : ℝ) (x : ℝ) : expMeasure lam {x} = 0 := by
  unfold expMeasure gammaMeasure
  exact (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)

lemma qfb_exp_Ioc (lam : ℝ) (hlam : 0 < lam) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    expMeasure lam (Ioc a b) = ENNReal.ofReal (Real.exp (-(lam * a)) - Real.exp (-(lam * b))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← measure_cdf (expMeasure lam), StieltjesFunction.measure_Ioc, cdf_expMeasure_eq hlam,
    cdf_expMeasure_eq hlam, if_pos ha, if_pos (ha.trans hab)]
  congr 1; ring

lemma qfb_exp_Ioi (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (ha : 0 ≤ a) :
    expMeasure lam (Ioi a) = ENNReal.ofReal (Real.exp (-(lam * a))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← measure_cdf (expMeasure lam), StieltjesFunction.measure_Ioi _ (tendsto_cdf_atTop _),
    cdf_expMeasure_eq hlam, if_pos ha]
  congr 1; ring

theorem exp_memoryless_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hTm : Measurable T)
    (hlaw : μ.map T = expMeasure lam) (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) :
    cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} := by
  have hA : MeasurableSet {ω | t₀ ≤ T ω} := hTm measurableSet_Ici
  rw [cond_apply hA]
  have e1 : μ {ω | t₀ ≤ T ω} = ENNReal.ofReal (Real.exp (-(lam * t₀))) := by
    rw [show {ω | t₀ ≤ T ω} = T ⁻¹' Ici t₀ from rfl, ← Measure.map_apply hTm measurableSet_Ici,
      hlaw, ← measure_congr (Ioi_ae_eq_Ici' (qfb_exp_noatoms lam t₀)), qfb_exp_Ioi lam hlam t₀ ht₀]
  have e2 : μ ({ω | t₀ ≤ T ω} ∩ {ω | T ω ≤ t₁}) =
      ENNReal.ofReal (Real.exp (-(lam * t₀)) - Real.exp (-(lam * t₁))) := by
    rw [show {ω | t₀ ≤ T ω} ∩ {ω | T ω ≤ t₁} = T ⁻¹' Icc t₀ t₁ from rfl,
      ← Measure.map_apply hTm measurableSet_Icc,
      hlaw, ← measure_congr (Ioc_ae_eq_Icc' (qfb_exp_noatoms lam t₀)), qfb_exp_Ioc lam hlam t₀ t₁ ht₀ ht]
  have e3 : μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} =
      ENNReal.ofReal (Real.exp (-(lam * 0)) - Real.exp (-(lam * (t₁ - t₀)))) := by
    rw [show {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} = T ⁻¹' Icc 0 (t₁ - t₀) from rfl,
      ← Measure.map_apply hTm measurableSet_Icc,
      hlaw, ← measure_congr (Ioc_ae_eq_Icc' (qfb_exp_noatoms lam 0)), qfb_exp_Ioc lam hlam 0 _ le_rfl (by linarith)]
  rw [e1, e2, e3, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.exp_neg, mul_sub, ← Real.exp_add, ← Real.exp_add]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring_nf
  simp

end QueueingFundamentals.Foundations

open QueueingFundamentals.Foundations


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hTm : Measurable T)
    (hlaw : μ.map T = expMeasure lam) (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) :
    cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} := by
  exact exp_memoryless_core μ lam hlam T hTm hlaw t₀ t₁ ht₀ ht
