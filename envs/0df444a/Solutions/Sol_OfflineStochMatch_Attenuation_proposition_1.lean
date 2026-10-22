-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:51.557468+00:00
-- url     : https://prove2.me/submissions/24ae8d2f-d2b2-477c-b031-52fef0c21bf8

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
set_option autoImplicit false

theorem solution (lam φ : ℝ → ℝ)
    (hlam : IntervalIntegrable lam MeasureTheory.volume 0 1)
    (hφ : IntervalIntegrable φ MeasureTheory.volume 0 1)
    (hlam_nonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam z)
    (hlam_anti : AntitoneOn lam (Set.Icc (0 : ℝ) 1))
    (zs : ℝ) (hzs : zs ∈ Set.Icc (0 : ℝ) 1)
    (hφ_pos : ∀ z ∈ Set.Icc (0 : ℝ) zs, 0 ≤ φ z)
    (hφ_neg : ∀ z ∈ Set.Icc zs 1, φ z ≤ 0) :
    lam zs * ∫ z in (0 : ℝ)..1, φ z ≤ ∫ z in (0 : ℝ)..1, lam z * φ z := by
  have hint : IntervalIntegrable (fun z => lam z * φ z) MeasureTheory.volume 0 1 := by
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun z => lam z * φ z)
        (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      rw [Set.uIoc_of_le zero_le_one]
      have h1 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hlam).aestronglyMeasurable
      have h2 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hφ).aestronglyMeasurable
      exact h1.mul h2
    refine IntervalIntegrable.mono_fun (hφ.const_mul (lam 0)) hmeas ?_
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
    have hz' : z ∈ Set.Icc (0:ℝ) 1 := ⟨hz.1.le, hz.2⟩
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hle : lam z ≤ lam 0 := hlam_anti h0 hz' hz.1.le
    have hnn := hlam_nonneg z hz'
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (hnn.trans hle)]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hnn : 0 ≤ ∫ z in (0 : ℝ)..1, (lam z - lam zs) * φ z := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro z hz
    rcases le_total z zs with h | h
    · have h1 : lam zs ≤ lam z := hlam_anti hz ⟨hz.1.trans h, hzs.2⟩ h
      exact mul_nonneg (sub_nonneg.2 h1) (hφ_pos z ⟨hz.1, h⟩)
    · have h1 : lam z ≤ lam zs := hlam_anti hzs hz h
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h1) (hφ_neg z ⟨h, hz.2⟩)
  have hsplit : ∫ z in (0 : ℝ)..1, (lam z - lam zs) * φ z =
      (∫ z in (0 : ℝ)..1, lam z * φ z) - lam zs * ∫ z in (0 : ℝ)..1, φ z := by
    have : ∀ z, (lam z - lam zs) * φ z = lam z * φ z - lam zs * φ z := fun z => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_sub hint (hφ.const_mul (lam zs)), intervalIntegral.integral_const_mul]
  linarith
