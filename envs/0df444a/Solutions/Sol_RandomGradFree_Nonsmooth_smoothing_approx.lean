-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.smoothing_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:45:54.403495+00:00
-- url     : https://prove2.me/submissions/6553aa24-1a48-4eaa-880d-6322199d9596

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

namespace RandomGradFree.Nonsmooth

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace in
theorem aux_sa_integral_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  set b := stdOrthonormalBasis ℝ E
  have h1 : (fun u : E => ‖u‖ ^ 2) = fun u => ∑ i, ⟪b i, u⟫ ^ 2 := by
    funext u; rw [b.sum_sq_inner_right]
  have hint : ∀ i, Integrable (fun u : E => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have hm : MemLp (fun u : E => innerSL ℝ (b i) u) 2 (stdGaussian E) :=
      (innerSL ℝ (b i)).comp_memLp' IsGaussian.memLp_two_id
    simpa [innerSL_apply_apply] using hm.integrable_sq
  have h2 : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have hv := variance_dual_stdGaussian (E := E) (innerSL ℝ (b i))
    rw [variance_of_integral_eq_zero (innerSL ℝ (b i)).continuous.aemeasurable
      (integral_strongDual_stdGaussian _), innerSL_apply_norm, b.orthonormal.1 i] at hv
    simpa [innerSL_apply_apply] using hv
  rw [h1, integral_finsetSum _ (fun i _ => hint i)]
  simp [h2]

theorem aux_sa_integral_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ∂(stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ E) := by
  have hm : MemLp (fun u : E => ‖u‖) 2 (stdGaussian E) := (IsGaussian.memLp_two_id).norm
  have hv := variance_nonneg (fun u : E => ‖u‖) (stdGaussian E)
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  rw [aux_sa_integral_norm_sq] at hv
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

end RandomGradFree.Nonsmooth

open RandomGradFree.Nonsmooth
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ * L₀ * Real.sqrt (Module.finrank ℝ E) := by
  have hcont : Continuous f := by
    have : LipschitzWith (Real.toNNReal L₀) f := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL₀]
      exact hLip a b
    exact this.continuous
  have hnorm_int : Integrable (fun u : E => ‖u‖) (stdGaussian E) :=
    (IsGaussian.integrable_id).norm
  have hbound : ∀ u : E, |f (x + μ • u) - f x| ≤ μ * L₀ * ‖u‖ := by
    intro u
    have := hLip (x + μ • u) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ] at this
    linarith
  have hg_int : Integrable (fun u : E => f (x + μ • u) - f x) (stdGaussian E) := by
    refine Integrable.mono' (hnorm_int.const_mul (μ * L₀)) ?_ ?_
    · exact (by fun_prop : Continuous fun u : E => f (x + μ • u) - f x).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]; exact hbound u
  have hf_int : Integrable (fun u : E => f (x + μ • u)) (stdGaussian E) := by
    have h : (fun u : E => f (x + μ • u)) = fun u => (f (x + μ • u) - f x) + f x := by
      funext u; ring
    rw [h]
    exact hg_int.add (integrable_const (f x))
  have heq : RandomGradFree.Shared.smoothing f μ x - f x
      = ∫ u, (f (x + μ • u) - f x) ∂(stdGaussian E) := by
    rw [integral_sub hf_int (integrable_const _), integral_const]
    simp [RandomGradFree.Shared.smoothing]
  rw [heq]
  calc |∫ u, (f (x + μ • u) - f x) ∂(stdGaussian E)|
      ≤ ∫ u, |f (x + μ • u) - f x| ∂(stdGaussian E) := by
        have := norm_integral_le_integral_norm (μ := stdGaussian E)
          (fun u : E => f (x + μ • u) - f x)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∫ u, μ * L₀ * ‖u‖ ∂(stdGaussian E) :=
        integral_mono hg_int.abs (hnorm_int.const_mul _) hbound
    _ = μ * L₀ * ∫ u, ‖u‖ ∂(stdGaussian E) := integral_const_mul _ _
    _ ≤ μ * L₀ * Real.sqrt (Module.finrank ℝ E) :=
        mul_le_mul_of_nonneg_left aux_sa_integral_norm_le (mul_nonneg hμ hL₀)
