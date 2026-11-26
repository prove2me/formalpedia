-- Prove2me | solution 1 for PVM.norm_sq_simpleIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:49.542555+00:00
-- url     : https://prove2.me/submissions/c0d8b163-f9f4-4cf8-8c3d-b0fb027ad01f

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_star_simpleIntegral_mul

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) (x : E) :
    ‖E_pvm.simpleIntegral f x‖ ^ 2 =
      ∑ z ∈ f.range, ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  rw [← ContinuousLinearMap.star_eq_adjoint]
  change (@inner ℂ E _
    ((star (E_pvm.simpleIntegral f) * E_pvm.simpleIntegral f) x) x).re = _
  rw [E_pvm.star_simpleIntegral_mul f]
  rw [sum_apply, sum_inner]
  rw [Complex.re_sum]
  have hzstar (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hterm (z : ℂ) :
      (@inner ℂ E _ (((star z * z) • E_pvm.proj (f ⁻¹' {z})) x) x).re =
        ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by
    rw [hzstar, smul_apply, inner_smul_left]
    have hrealstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [starRingEnd_apply, hrealstar]
    change ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re -
        0 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).im = _
    ring
  simpa only [] using
    (Finset.sum_congr (s₁ := f.range) (s₂ := f.range) rfl (fun z hz => hterm z))
end PVM
