-- Prove2me | solution 1 for QChernoff.Trace.resolvent_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:04:18.66481+00:00
-- url     : https://prove2.me/submissions/507d5b84-3f14-48d0-bfed-a2da9f9921e1

import Mathlib


lemma unit_of_nonneg_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : H →L[ℂ] H) (hP : 0 ≤ P) (x : ℝ) (hx : 0 < x) :
    IsUnit (P + (x : ℂ) • (1 : H →L[ℂ] H)) := by
  have h1 : IsStrictlyPositive ((x : ℂ) • (1 : H →L[ℂ] H)) := by
    have := IsStrictlyPositive.smul (𝕜 := ℝ) hx (isStrictlyPositive_one (A := H →L[ℂ] H))
    simpa [Complex.coe_smul] using this
  exact (h1.nonneg_add hP).isUnit

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable
        (deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      IntervalIntegrable
        (fun t : ℝ => x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      A * Ring.inverse (A + (x : ℂ) • 1) - B * Ring.inverse (B + (x : ℂ) • 1) =
        ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t ∧
      ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t =
        ∫ t in (0 : ℝ)..1, x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)) := by
  set f : ℝ → H →L[ℂ] H := fun τ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)
    with hf
  set k : ℝ → H →L[ℂ] H := fun t => x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)) with hk
  have hunit : ∀ t ∈ Set.uIcc (0:ℝ) 1, IsUnit (B + t • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    apply unit_of_nonneg_add _ _ x hx
    have : B + t • (A - B) = (1 - t) • B + t • A := by
      simp [sub_smul, smul_sub]; abel
    rw [this]
    exact add_nonneg (smul_nonneg (by linarith [ht.2]) hB) (smul_nonneg ht.1 hA)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (k t) t := by
    intro t ht
    obtain ⟨u, hu⟩ := hunit t ht
    have hg : HasDerivAt (fun τ : ℝ => B + τ • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)) (A - B) t := by
      have := ((hasDerivAt_id t).smul_const (A - B)).const_add B
      simpa using this.add_const ((x : ℂ) • (1 : H →L[ℂ] H))
    have hinv := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
    rw [← Ring.inverse_unit, hu] at hinv
    have hR : HasDerivAt (fun τ : ℝ => Ring.inverse (B + τ • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)))
        (-(Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1))) t := by
      have := hinv.comp_hasDerivAt t hg
      simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply] at this
      exact this
    have hB' : HasDerivAt (fun τ : ℝ => B + τ • (A - B)) (A - B) t := by
      simpa using ((hasDerivAt_id t).smul_const (A - B)).const_add B
    refine (hB'.fun_mul hR).congr_deriv ?_
    set R := Ring.inverse (B + t • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H))
    have hMR : (B + t • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)) * R = 1 := by
      exact Ring.mul_inverse_cancel _ (hunit t ht)
    have : (A - B) * R = (B + t • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)) * R * (A - B) * R := by
      rw [hMR, one_mul]
    rw [this]
    simp only [hk, add_mul, mul_neg, smul_mul_assoc, one_mul, mul_assoc]
    rw [← Complex.coe_smul]
    abel
  have hcont : ContinuousOn k (Set.uIcc 0 1) := by
    intro t ht
    obtain ⟨u, hu⟩ := hunit t ht
    have hg : Continuous (fun τ : ℝ => B + τ • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H)) := by
      fun_prop
    have hinvc : ContinuousAt (fun τ : ℝ => Ring.inverse (B + τ • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H))) t := by
      have := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).continuousAt
      rw [hu] at this
      exact ContinuousAt.comp (f := fun τ : ℝ => B + τ • (A - B) + (x : ℂ) • (1 : H →L[ℂ] H))
        this hg.continuousAt
    exact (((hinvc.mul continuousAt_const).mul hinvc).const_smul x).continuousWithinAt
  have hderiv_eq : Set.EqOn (deriv f) k (Set.uIcc 0 1) := fun t ht => (hderiv t ht).deriv
  have hint : IntervalIntegrable k MeasureTheory.volume 0 1 := hcont.intervalIntegrable
  have hint' : IntervalIntegrable (deriv f) MeasureTheory.volume 0 1 :=
    (hcont.congr hderiv_eq).intervalIntegrable
  refine ⟨hint', hint, ?_, intervalIntegral.integral_congr hderiv_eq⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hderiv_eq ht) ▸ hderiv t ht) hint']
  simp [hf]
