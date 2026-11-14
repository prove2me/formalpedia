-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.integral_of_exponential_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:14:52.966215+00:00
-- url     : https://prove2.me/submissions/5db198c3-d6e9-4021-a0e5-a4e8facba2e9

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (q β : ℝ) (hq : 1 ≤ q) (hβ : 0 < β)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < f ω} ≤ q * Real.exp (-β*t)) :
    (∫ ω, f ω ∂μ) ≤ (Real.log q + 1) / β := by
  let P : ℝ → ℝ := fun t => μ.real {ω | t < f ω}
  let T := Real.log q / β
  have hqpos : 0 < q := by linarith
  have hT : 0 ≤ T := div_nonneg (Real.log_nonneg hq) (le_of_lt hβ)
  have hPmeas : Measurable P := by
    unfold P Measure.real
    apply Measurable.ennreal_toReal
    exact Antitone.measurable (fun _ _ hst => measure_mono (fun _ h => lt_of_le_of_lt hst h))
  have hP0 (t : ℝ) : 0 ≤ P t := measureReal_nonneg
  have hP1 (t : ℝ) : P t ≤ 1 := measureReal_le_one
  have hsmall : IntegrableOn P (Ioc 0 T) volume := by
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hPmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hP0 t)]; exact hP1 t)
  have hlargeexp : IntegrableOn (fun t : ℝ => q * Real.exp (-β*t)) (Ioi T) volume := by
    have h := (integrableOn_exp_mul_Ioi (by linarith : -β < 0) T).const_mul q
    exact h
  have hlarge : IntegrableOn P (Ioi T) volume := by
    apply hlargeexp.mono' hPmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 t)]
    exact htail t (le_trans hT (le_of_lt ht))
  have hsmallbound : (∫ t in Ioc 0 T, P t) ≤ T := by
    have h := setIntegral_mono_on hsmall (integrableOn_const (μ := volume) (s := Ioc 0 T) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
      (fun t ht => hP1 t)
    simpa [integral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hT] using h
  have hlargebound : (∫ t in Ioi T, P t) ≤ 1 / β := by
    have h := setIntegral_mono_on hlarge hlargeexp measurableSet_Ioi
      (fun t ht => htail t (le_trans hT (le_of_lt ht)))
    have he : q * Real.exp (-β*T) = 1 := by
      have hbt : β*T = Real.log q := by dsimp [T]; field_simp
      rw [show -β*T = -(β*T) by ring, hbt, Real.exp_neg, Real.exp_log hqpos]
      exact mul_inv_cancel₀ (ne_of_gt hqpos)
    have heval : (∫ t in Ioi T, q * Real.exp (-β*t)) = 1 / β := by
      rw [integral_const_mul]
      have hh := integral_exp_mul_Ioi (a := -β) (by linarith) T
      rw [hh]
      calc
        q * (-Real.exp (-β*T) / -β) = (q * Real.exp (-β*T)) / β := by ring
        _ = 1 / β := by rw [he]
    rw [heval] at h
    exact h
  have hsplit : (∫ t in Ioi 0, P t) = (∫ t in Ioc 0 T, P t) + ∫ t in Ioi T, P t := by
    rw [← Ioc_union_Ioi_eq_Ioi hT]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hlarge
  rw [hf.integral_eq_integral_meas_lt hnonneg]
  change (∫ t in Ioi 0, P t) ≤ _
  rw [hsplit]
  have : T + 1 / β = (Real.log q + 1) / β := by dsimp [T]; ring
  linarith
