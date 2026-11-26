-- Prove2me | solution 1 for PVM.norm_simpleIntegral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:25.811906+00:00
-- url     : https://prove2.me/submissions/37894842-f267-4ead-9de7-694f176b47f8

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_sum_proj_fiber_eq_one
import Theorems.Thm_PVM_norm_sq_simpleIntegral

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t‖ ≤ C) : ‖E_pvm.simpleIntegral f‖ ≤ C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hbdd 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hweight_nonneg (z : ℂ) :
      0 ≤ (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
    exact
      ((ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z}) (f.measurableSet_fiber z)).2).mpr
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
          (f.measurableSet_fiber z)).1).re_inner_nonneg_left x
  have hsum_weight :
      ∑ z ∈ f.range, (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re = ‖x‖ ^ 2 := by
    have h := congrArg
      (fun A : E →L[ℂ] E => (@inner ℂ E _ (A x) x).re)
      (E_pvm.sum_proj_fiber_eq_one f)
    rw [sum_apply, sum_inner, Complex.re_sum] at h
    change (∑ z ∈ f.range,
      (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re) =
        (@inner ℂ E _ x x).re at h
    calc
      ∑ z ∈ f.range,
          (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re =
          (@inner ℂ E _ x x).re := h
      _ = ‖x‖ ^ 2 := by
        change RCLike.re (@inner ℂ E _ x x) = ‖x‖ ^ 2
        exact @inner_self_eq_norm_sq ℂ E _ _ _ x
  have hsquare : ‖E_pvm.simpleIntegral f x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [E_pvm.norm_sq_simpleIntegral f x]
    calc
      ∑ z ∈ f.range,
          ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re ≤
          ∑ z ∈ f.range,
            C ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_right _ (hweight_nonneg z)
        apply (sq_le_sq₀ (norm_nonneg z) hC).mpr
        rw [SimpleFunc.mem_range] at hz
        obtain ⟨t, rfl⟩ := hz
        exact hbdd t
      _ = C ^ 2 * ∑ z ∈ f.range,
          (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
        rw [Finset.mul_sum]
      _ = C ^ 2 * ‖x‖ ^ 2 := by rw [hsum_weight]
      _ = (C * ‖x‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp hsquare
end PVM
