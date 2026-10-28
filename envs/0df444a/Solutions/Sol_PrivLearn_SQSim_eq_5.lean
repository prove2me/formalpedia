-- Prove2me | solution 1 for PrivLearn.SQSim.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:06:11.987982+00:00
-- url     : https://prove2.me/submissions/fd588feb-d1f4-4b5f-a897-1201542326b5

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open PrivLearn.SQSim
open MeasureTheory

theorem solution {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
    (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w) (u₀ : Dom) (ε β : ℝ) (t : ℕ)
    (hε : 0 < ε) (hβ : 0 < β) (ht : 1 ≤ t) (hR : IsLocalRandomizerPMF R ε)
    (w : W) (hq : 0 < R u₀ w) (v : ℝ)
    (hv : IsSQAnswer P (sqQuery (fun u => (R u w).toReal) u₀ ε) (simTolerance ε β t) v) :
    (∀ u, sqQuery (fun u => (R u w).toReal) u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
    |sqEstimate (fun u => (R u w).toReal) u₀ ε v - pTarget P R w| ≤
      simPhi β t * pTarget P R w := by
  have hE1 : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
  have hEpos : 0 < Real.exp ε := Real.exp_pos ε
  have he : Real.exp (-ε) = (Real.exp ε)⁻¹ := Real.exp_neg ε
  have hr0 : 0 < (R u₀ w).toReal := ENNReal.toReal_pos hq.ne' (PMF.apply_ne_top _ _)
  have hup : ∀ u, (R u w).toReal ≤ Real.exp ε * (R u₀ w).toReal := by
    intro u
    have h := hR u u₀ w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hlo : ∀ u, (R u₀ w).toReal ≤ Real.exp ε * (R u w).toReal := by
    intro u
    have h := hR u₀ u w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hinv : (Real.exp ε)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hinv0 : 0 < (Real.exp ε)⁻¹ := inv_pos.mpr hEpos
  have hD : 0 < Real.exp ε - Real.exp (-ε) := by rw [he]; linarith
  have hrD : 0 < (R u₀ w).toReal * (Real.exp ε - Real.exp (-ε)) := mul_pos hr0 hD
  have hEE : Real.exp ε * (Real.exp ε)⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
  have hlo' : ∀ u, (Real.exp ε)⁻¹ * (R u₀ w).toReal ≤ (R u w).toReal := by
    intro u
    have := hlo u
    rw [inv_mul_le_iff₀ hEpos]; exact this
  refine ⟨fun u => ?_, ?_⟩
  · unfold sqQuery
    constructor
    · rw [le_div_iff₀ hrD]
      have := hlo' u
      rw [he]
      nlinarith
    · rw [div_le_iff₀ hrD]
      have := hup u
      rw [he]
      nlinarith
  · have hrm : Measurable fun u => (R u w).toReal := (hmeas w).ennreal_toReal
    have hrI : Integrable (fun u => (R u w).toReal) P := by
      refine Integrable.of_bound hrm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun u => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (R u) w)
    have hint : ∫ u, sqQuery (fun u => (R u w).toReal) u₀ ε u ∂P
        = (pTarget P R w - (R u₀ w).toReal) / ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε))) := by
      unfold sqQuery pTarget
      rw [integral_div, integral_sub hrI (integrable_const _)]
      simp
    have hp : (Real.exp ε)⁻¹ * (R u₀ w).toReal ≤ pTarget P R w := by
      unfold pTarget
      have := integral_mono (integrable_const ((Real.exp ε)⁻¹ * (R u₀ w).toReal)) hrI hlo'
      simpa using this
    unfold IsSQAnswer at hv
    rw [hint] at hv
    have hest : sqEstimate (fun u => (R u w).toReal) u₀ ε v - pTarget P R w
        = ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε))) *
          (v - (pTarget P R w - (R u₀ w).toReal) / ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε)))) := by
      unfold sqEstimate
      field_simp
      ring
    rw [hest, abs_mul, abs_of_pos hrD]
    have h1 := mul_le_mul_of_nonneg_left hv hrD.le
    refine le_trans h1 ?_
    unfold simTolerance simPhi
    have htr : (0 : ℝ) < t := by exact_mod_cast ht
    have hE2 : Real.exp (2 * ε) = Real.exp ε * Real.exp ε := by rw [← Real.exp_add]; ring_nf
    rw [hE2, he]
    have key : (Real.exp ε - (Real.exp ε)⁻¹) / (Real.exp ε * Real.exp ε) ≤ (Real.exp ε)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc (R u₀ w).toReal * (Real.exp ε - (Real.exp ε)⁻¹) * (β / (3 * (Real.exp ε * Real.exp ε) * t))
        = (β / (3 * t)) * ((R u₀ w).toReal * ((Real.exp ε - (Real.exp ε)⁻¹) / (Real.exp ε * Real.exp ε))) := by
          field_simp
      _ ≤ (β / (3 * t)) * ((R u₀ w).toReal * (Real.exp ε)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left key hr0.le
      _ ≤ β / (3 * t) * pTarget P R w := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
