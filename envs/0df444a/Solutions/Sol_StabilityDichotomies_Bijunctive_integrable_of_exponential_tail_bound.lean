-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.integrable_of_exponential_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:14:54.213028+00:00
-- url     : https://prove2.me/submissions/b41ef197-0832-4b7f-a059-37a3a158aa95

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 < β)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < f ω} ≤ q * Real.exp (-β*t)) :
    Integrable f μ := by
  have hexp : IntegrableOn (fun t : ℝ => q * Real.exp (-β*t)) (Ioi 0) volume := by
    exact (integrableOn_exp_mul_Ioi (by linarith : -β < 0) 0).const_mul q
  have hfinite : (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < f ω}) < ∞ := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (q * Real.exp (-β*t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hh := ENNReal.ofReal_le_ofReal (htail t (le_of_lt ht))
        change ENNReal.ofReal ((μ {ω | t < f ω}).toReal) ≤ _ at hh
        rw [ENNReal.ofReal_toReal (measure_ne_top μ _)] at hh
        exact hh
      _ < ∞ := hexp.lintegral_lt_top
  have hfin : HasFiniteIntegral f μ := by
    apply (hasFiniteIntegral_iff_ofReal hnonneg).mpr
    rw [lintegral_eq_lintegral_meas_lt μ hnonneg hf]
    exact hfinite
  exact ⟨hf.aestronglyMeasurable,hfin⟩
