-- Prove2me | solution 1 for QChernoff.Trace.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:10:56.702131+00:00
-- url     : https://prove2.me/submissions/1aaf8fec-4bc5-42e8-96df-6e058c006fdc

import Mathlib
open Real Set MeasureTheory

lemma beta_real (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ y in Ioo (0:ℝ) 1, y ^ (t - 1) * (1 - y) ^ (-t) = π / Real.sin (t * π) := by
  apply Complex.ofReal_injective
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (t:ℂ)) (t := 1 - (t:ℂ))
    (by simpa using ht0) (by simpa using ht1)
  rw [add_sub_cancel, Complex.Gamma_one, one_mul, Complex.Gamma_mul_Gamma_one_sub] at hB
  have : ((π / Real.sin (t * π) : ℝ) : ℂ) = (π : ℂ) / Complex.sin (π * t) := by
    push_cast; ring_nf
  rw [this, hB, Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  have h1 : 0 ≤ y := hy.1.le
  have h2 : 0 ≤ 1 - y := by linarith [hy.2]
  push_cast
  rw [Complex.ofReal_cpow h1, Complex.ofReal_cpow h2]
  push_cast
  ring_nf
lemma subst_lem (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ x in Ioi (0:ℝ), rpowIntegrand₀₁ t x 1 = ∫ y in Ioo (0:ℝ) 1, y ^ (t - 1) * (1 - y) ^ (-t) := by
  have himg : (fun y : ℝ => y / (1 - y)) '' Ioo 0 1 = Ioi 0 := by
    ext x; constructor
    · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
      exact div_pos hy0 (by linarith)
    · intro hx
      have hx : 0 < x := hx
      refine ⟨x / (1 + x), ⟨div_pos hx (by linarith), ?_⟩, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · simp only
        field_simp
        ring
  have hderiv : ∀ y ∈ Ioo (0:ℝ) 1, HasDerivWithinAt (fun y : ℝ => y / (1 - y))
      (1 / (1 - y) ^ 2) (Ioo 0 1) y := by
    intro y hy
    have hne : (1 - y) ≠ 0 := by linarith [hy.2]
    have := (hasDerivAt_id y).div ((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)) hne
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp
  have hinj : InjOn (fun y : ℝ => y / (1 - y)) (Ioo 0 1) := by
    intro a ha b hb hab
    simp only at hab
    have h1 : (1 - a) ≠ 0 := by linarith [ha.2]
    have h2 : (1 - b) ≠ 0 := by linarith [hb.2]
    rw [div_eq_div_iff h1 h2] at hab
    linarith
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  simp only [smul_eq_mul, rpowIntegrand₀₁]
  rw [abs_of_pos (by positivity), Real.div_rpow hy0.le hy1.le, Real.rpow_neg hy1.le,
    Real.rpow_sub_one hy0.ne']
  field_simp
  ring

lemma cfc_integrand_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (x : ℝ) (hx : 0 < x) :
    cfc (rpowIntegrand₀₁ t x) A = x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1)) := by
  have hspec : spectrum ℝ A ⊆ Ici 0 := fun y hy => by grind
  have h1 : cfc (rpowIntegrand₀₁ t x) A = cfc (fun y => x ^ (t - 1) * (y * (y + x)⁻¹)) A := by
    refine cfc_congr (fun y hy => ?_)
    have hy : 0 ≤ y := hspec hy
    simp only [rpowIntegrand₀₁]
    rw [Real.rpow_sub_one hx.ne']
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => (y + x)⁻¹) (spectrum ℝ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) (fun y hy => ?_)
    have := hspec hy; simp only [mem_Ici] at this; linarith
  rw [h1, cfc_const_mul _ _ _ (by fun_prop), cfc_mul (fun y => y) _ _ (by fun_prop) hcont, cfc_id' ℝ A,
    cfc_inv (f := fun y : ℝ => y + x) (a := A) (fun y hy => by have := hspec hy; simp only [mem_Ici] at this; linarith)
      (by fun_prop),
    cfc_add_const _ _ _ (by fun_prop), cfc_id' ℝ A, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1))) (Set.Ioi 0) ∧
      A ^ t = (Real.sin (t * Real.pi) / Real.pi) •
        ∫ x in Set.Ioi (0 : ℝ), x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1)) := by
  have hp : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, ht1⟩
  have hspec : spectrum ℝ A ⊆ Ici 0 := fun y hy => by grind
  let f : ℝ → ℝ → ℝ := fun x => rpowIntegrand₀₁ t x
  let maxr := sSup (spectrum ℝ A)
  have hmaxr : ∀ z ∈ spectrum ℝ A, z ≤ maxr := fun z hz =>
    le_csSup (IsCompact.bddAbove (spectrum.isCompact _)) hz
  let bound (x : ℝ) := ‖f x (max maxr 0)‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : ℝ) ×ˢ spectrum ℝ A) :=
    continuousOn_rpowIntegrand₀₁_uncurry hp (spectrum ℝ A) hspec
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), ∀ z ∈ spectrum ℝ A, ‖f x z‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hz' : 0 ≤ z := hspec hz
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg ht0 (le_of_lt hx) hz'),
        Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg ht0 (le_of_lt hx) (le_max_right _ _))]
    exact rpowIntegrand₀₁_monotoneOn hp (le_of_lt hx) hz' (Set.mem_Ici.mpr (le_max_right _ _))
      ((hmaxr z hz).trans (le_max_left _ _))
  have hbint : HasFiniteIntegral bound (volume.restrict (Ioi (0:ℝ))) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (integrableOn_rpowIntegrand₀₁_Ioi hp (le_max_right maxr 0)).2
  have heq : EqOn (fun x => cfc (f x) A)
      (fun x : ℝ => x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1))) (Ioi 0) :=
    fun x hx => cfc_integrand_eq A hA t ht0 ht1 x hx
  have hint := integrableOn_cfc measurableSet_Ioi f bound A hf hbound hbint
  refine ⟨hint.congr_fun heq measurableSet_Ioi, ?_⟩
  have hI : ∫ x in Ioi (0:ℝ), rpowIntegrand₀₁ t x 1 = π / Real.sin (t * π) := by
    rw [subst_lem t ht0 ht1, beta_real t ht0 ht1]
  have hsin : 0 < Real.sin (t * π) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hgc : ContinuousOn (fun r => ∫ x in Ioi (0:ℝ), f x r) (spectrum ℝ A) := by
    have : ContinuousOn (fun r : ℝ => (π / Real.sin (t * π)) * r ^ t) (spectrum ℝ A) :=
      ContinuousOn.mul continuousOn_const
        (ContinuousOn.rpow_const continuousOn_id (fun _ _ => Or.inr ht0.le))
    refine this.congr (fun r hr => ?_)
    simp only [f]
    rw [rpow_eq_const_mul_integral hp (hspec hr), hI, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact (div_pos Real.pi_pos hsin).ne'
  rw [← setIntegral_congr_fun measurableSet_Ioi heq,
    ← cfc_setIntegral measurableSet_Ioi f bound A hf hbound hbint, CFC.rpow_eq_cfc_real hA,
    ← cfc_const_mul _ _ A hgc]
  refine cfc_congr (fun y hy => ?_)
  rw [rpow_eq_const_mul_integral hp (hspec hy), hI, inv_div]
