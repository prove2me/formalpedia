-- Prove2me | solution 1 for RandomOrderCRS.proposition_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:43:16.465438+00:00
-- url     : https://prove2.me/submissions/425b7e24-b6c5-48b2-9bda-c8b680620e77

import Mathlib

open MeasureTheory in
theorem solution (lam φ : ℝ → ℝ) (hlam : IntervalIntegrable lam MeasureTheory.volume 0 1)
    (hφ : IntervalIntegrable φ MeasureTheory.volume 0 1)
    (hlam0 : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam z) (hanti : AntitoneOn lam (Set.Icc (0 : ℝ) 1))
    (zc : ℝ) (hzc : zc ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ z ∈ Set.Icc 0 zc, 0 ≤ φ z)
    (hneg : ∀ z ∈ Set.Icc zc 1, φ z ≤ 0) :
    lam zc * ∫ z in (0 : ℝ)..1, φ z ≤ ∫ z in (0 : ℝ)..1, lam z * φ z := by
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hprod : IntervalIntegrable (fun z => lam z * φ z) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hlam hφ ⊢
    refine hφ.bdd_mul hlam.aestronglyMeasurable (c := lam 0) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro z hz
    have hz' : z ∈ Set.Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hlam0 z hz')]
    exact hanti h01 hz' hz.1.le
  have hdiff : (∫ z in (0 : ℝ)..1, lam z * φ z) - lam zc * ∫ z in (0 : ℝ)..1, φ z =
      ∫ z in (0 : ℝ)..1, (lam z - lam zc) * φ z := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hprod
      (hφ.const_mul _)]
    congr 1; funext z; ring
  have hnn : 0 ≤ ∫ z in (0 : ℝ)..1, (lam z - lam zc) * φ z := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro z hz
    rcases le_total z zc with h | h
    · have h1 : lam zc ≤ lam z := hanti hz hzc h
      have h2 := hpos z ⟨hz.1, h⟩
      exact mul_nonneg (by linarith) h2
    · have h1 : lam z ≤ lam zc := hanti hzc hz h
      have h2 := hneg z ⟨h, hz.2⟩
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) h2
  linarith
