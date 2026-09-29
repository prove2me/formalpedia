-- Prove2me | solution 1 for RandomGradFree.Smooth.smoothing_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:08:51.838847+00:00
-- url     : https://prove2.me/submissions/28a1eaed-108b-41c0-ac3f-5374fd171e8b

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

open scoped RealInnerProductSpace

theorem aux_sa_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (x v : E) :
    |f (x + v) - f x - ⟪gradient f x, v⟫| ≤ L₁ / 2 * ‖v‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪gradient f x, v⟫
  let g' : ℝ → ℝ := fun t => ⟪gradient f (x + t • v), v⟫ - ⟪gradient f x, v⟫
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • v)))
        (x + t • v) :=
      hasGradientAt_iff_hasFDerivAt.mp (hdiff (x + t • v)).hasGradientAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt g
        ((InnerProductSpace.toDual ℝ E (gradient f (x + t • v))) v - 1 * ⟪gradient f x, v⟫) t :=
      (h3.sub_const (f x)).sub ((hasDerivAt_id' t).mul_const _)
    refine h4.congr_deriv ?_
    simp [g']
  let B : ℝ → ℝ := fun t => L₁ / 2 * ‖v‖ ^ 2 * t ^ 2
  let B' : ℝ → ℝ := fun t => L₁ * ‖v‖ ^ 2 * t
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have h : HasDerivAt B (L₁ / 2 * ‖v‖ ^ 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      (hasDerivAt_pow 2 t).const_mul _
    refine h.congr_deriv ?_
    simp only [B']; norm_num; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := g)
    (f' := g')
    (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => (hg t).hasDerivWithinAt) (B := B) (B' := B') (by simp [g, B]) hB ?_
    (x := 1) (by simp)
  · simpa [g, B, Real.norm_eq_abs] using key
  · intro t ht
    rw [Real.norm_eq_abs]
    have : g' t = ⟪gradient f (x + t • v) - gradient f x, v⟫ := by simp [g', inner_sub_left]
    rw [this]
    calc |⟪gradient f (x + t • v) - gradient f x, v⟫|
        ≤ ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (L₁ * ‖x + t • v - x‖) * ‖v‖ := by gcongr; exact hgrad _ _
      _ = B' t := by simp [B', norm_smul, abs_of_nonneg ht.1]; ring

theorem aux_sa_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hmem : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hone : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian] at h
    have hm : (stdGaussian E)[id] = 0 := by simp
    simp only [hm, sub_zero] at h
    change ⟪b i, b i⟫ = _ at h
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simp only [one_pow] at h
    rw [h]
    congr 1
    ext u
    ring
  have hint : ∀ i, Integrable (fun u => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have : MemLp (fun u : E => ⟪b i, u⟫) 2 (stdGaussian E) :=
      (innerSL ℝ (b i)).comp_memLp' hmem
    exact this.integrable_sq
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E)
      = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [hone]

end RandomGradFree.Smooth

open RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by
  set G := gradient f x
  let h : E → ℝ := fun u => f (x + μ • u) - f x - μ * inner ℝ G u
  have hcont : Continuous f := hdiff.continuous
  have hhcont : Continuous h := by
    have : Continuous fun u : E => inner ℝ G u := continuous_const.inner continuous_id
    exact ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).sub
      continuous_const).sub (continuous_const.mul this)
  have hbound : ∀ u, |h u| ≤ μ ^ 2 / 2 * L₁ * ‖u‖ ^ 2 := by
    intro u
    have := aux_sa_descent f L₁ hdiff hgrad x (μ • u)
    have e : inner ℝ G (μ • u) = μ * inner ℝ G u := real_inner_smul_right _ _ _
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at this
    calc |h u| ≤ L₁ / 2 * (μ * ‖u‖) ^ 2 := this
      _ = μ ^ 2 / 2 * L₁ * ‖u‖ ^ 2 := by ring
  have hmem : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hsqint : Integrable (fun u : E => ‖u‖ ^ 2) (stdGaussian E) :=
    hmem.integrable_norm_pow (by norm_num)
  have hhint : Integrable h (stdGaussian E) := by
    refine Integrable.mono' (hsqint.const_mul (μ ^ 2 / 2 * L₁)) hhcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact hbound u)
  have hinner_int : Integrable (fun u : E => inner ℝ G u) (stdGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).const_inner G
  have hmean : ∫ u, inner ℝ G u ∂(stdGaussian E) = 0 := by
    have := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id (μ := stdGaussian E)) G
    simpa using this
  have hsplit : RandomGradFree.Shared.smoothing f μ x - f x = ∫ u, h u ∂(stdGaussian E) := by
    unfold RandomGradFree.Shared.smoothing
    have e : (fun u => f (x + μ • u)) = fun u => h u + (f x + μ * inner ℝ G u) := by
      ext u; simp [h]
    rw [e, integral_add (f := h) (g := fun u => f x + μ * inner ℝ G u) hhint
      ((integrable_const _).add (hinner_int.const_mul μ)),
      integral_add (f := fun _ => f x) (g := fun u => μ * inner ℝ G u) (integrable_const _)
        (hinner_int.const_mul μ), integral_const_mul, hmean]
    simp
  rw [hsplit, ← Real.norm_eq_abs]
  calc ‖∫ u, h u ∂(stdGaussian E)‖
      ≤ ∫ u, μ ^ 2 / 2 * L₁ * ‖u‖ ^ 2 ∂(stdGaussian E) :=
        norm_integral_le_of_norm_le (hsqint.const_mul _)
          (Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact hbound u))
    _ = μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by rw [integral_const_mul, aux_sa_sq]
