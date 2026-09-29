-- Prove2me | solution 1 for RandomGradFree.Accelerated.smoothing_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:44:17.191434+00:00
-- url     : https://prove2.me/submissions/a9c0e632-eda9-4ef2-a8d2-515ac6c76d24

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

open scoped RealInnerProductSpace in
theorem aux_sa_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hmem : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hint : ∀ i, Integrable (fun u : E => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (b i)) 2 (by simp)
    simpa using this.integrable_sq
  have h1 : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply (μ := stdGaussian E) hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian, show (∫ x, id x ∂(stdGaussian E)) = 0 from integral_id_stdGaussian] at h
    simp only [sub_zero] at h
    have e : (innerSL ℝ (b i)) (b i) = 1 := by
      simp [b.orthonormal.1 i]
    rw [e] at h
    rw [h]
    congr 1
    ext u
    ring
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [h1]


open scoped RealInnerProductSpace in
theorem aux_sa_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (x h : E) :
    |f (x + h) - f x - ⟪gradient f x, h⟫| ≤ L₁ / 2 * ‖h‖ ^ 2 := by
  set φ : ℝ → ℝ := fun t => f (x + t • h) - f x - t * ⟪gradient f x, h⟫ with hφ
  have hderiv : ∀ t : ℝ, HasDerivAt φ (⟪gradient f (x + t • h), h⟫ - ⟪gradient f x, h⟫) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • h))) (x + t • h) :=
      (hdiff _).hasGradientAt.hasFDerivAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, h⟫) ⟪gradient f x, h⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, h⟫
    have h5 := (h3.sub_const (f x)).sub h4
    exact h5
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := φ)
    (f' := fun t => ⟪gradient f (x + t • h), h⟫ - ⟪gradient f x, h⟫)
    (B := fun t => L₁ / 2 * t ^ 2 * ‖h‖ ^ 2) (B' := fun t => L₁ * t * ‖h‖ ^ 2)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp [hφ])
    (by
      intro t
      have := ((hasDerivAt_pow 2 t).const_mul (L₁ / 2)).mul_const (‖h‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    (by
      intro t ht
      rw [← inner_sub_left, Real.norm_eq_abs]
      calc |⟪gradient f (x + t • h) - gradient f x, h⟫|
          ≤ ‖gradient f (x + t • h) - gradient f x‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ (L₁ * ‖(x + t • h) - x‖) * ‖h‖ := by
            gcongr; exact hgrad _ _
        _ = L₁ * t * ‖h‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring)
  have := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [hφ, Real.norm_eq_abs] using this

open scoped RealInnerProductSpace in
theorem aux_sa_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by
  set g := gradient f x with hg
  have hcont : Continuous f := hdiff.continuous
  set R : E → ℝ := fun u => f (x + μ • u) - f x - ⟪g, μ • u⟫ with hRdef
  have hR : ∀ u, |R u| ≤ L₁ / 2 * μ ^ 2 * ‖u‖ ^ 2 := by
    intro u
    have := aux_sa_descent f L₁ hdiff hgrad x (μ • u)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [hRdef]
    linarith
  have hsq : Integrable (fun u : E => ‖u‖ ^ 2) (stdGaussian E) := by
    have h2 : MemLp id ((2 : ℕ) : ENNReal) (stdGaussian E) := by
      simpa using (IsGaussian.memLp_two_id (μ := stdGaussian E))
    simpa using h2.integrable_norm_pow (by norm_num)
  have hRcont : Continuous R := by
    simp only [hRdef]
    fun_prop
  have hRint : Integrable R (stdGaussian E) := by
    refine Integrable.mono' (hsq.const_mul (L₁ / 2 * μ ^ 2)) hRcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact hR u)
  have hid : Integrable (fun u : E => μ • u) (stdGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).smul μ
  have hlin : Integrable (fun u : E => ⟪g, μ • u⟫) (stdGaussian E) := hid.const_inner g
  have hlin0 : ∫ u, ⟪g, μ • u⟫ ∂(stdGaussian E) = 0 := by
    rw [integral_inner hid, integral_smul, integral_id_stdGaussian]
    simp
  have hsplit : RandomGradFree.Shared.smoothing f μ x - f x = ∫ u, R u ∂(stdGaussian E) := by
    unfold RandomGradFree.Shared.smoothing
    have e : ∀ u, f (x + μ • u) = (R u + f x) + ⟪g, μ • u⟫ := by
      intro u; simp only [hRdef]; ring
    simp_rw [e]
    have hRc : Integrable (fun u => R u + f x) (stdGaussian E) := hRint.add (integrable_const _)
    rw [integral_add hRc hlin, integral_add hRint (integrable_const _), integral_const, hlin0]
    simp
  rw [hsplit]
  calc |∫ u, R u ∂(stdGaussian E)| ≤ ∫ u, |R u| ∂(stdGaussian E) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, L₁ / 2 * μ ^ 2 * ‖u‖ ^ 2 ∂(stdGaussian E) :=
        integral_mono hRint.abs (hsq.const_mul _) hR
    _ = L₁ / 2 * μ ^ 2 * Module.finrank ℝ E := by
        rw [integral_const_mul, aux_sa_second_moment]
    _ = μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by ring

end RandomGradFree.Accelerated

open RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E :=
  aux_sa_main f L₁ hL₁ hdiff hgrad μ hμ x
