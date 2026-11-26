-- Prove2me | solution 1 for PVM.star_simpleIntegral_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:01.891012+00:00
-- url     : https://prove2.me/submissions/0cfbeb71-3b71-4629-a070-ceb077af15b6

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_proj_fiber_mul_proj_fiber

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    star (E_pvm.simpleIntegral f) * E_pvm.simpleIntegral f =
      ∑ z ∈ f.range, (star z * z) • E_pvm.proj (f ⁻¹' {z}) := by
  classical
  rw [PVM.simpleIntegral, star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [star_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
    (f.measurableSet_fiber z)).1.star_eq, Finset.mul_sum]
  rw [Finset.sum_eq_single z]
  · rw [smul_mul_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
      (f.measurableSet_fiber z)).2.eq]
  · intro w hw hwz
    rw [smul_mul_smul, E_pvm.proj_fiber_mul_proj_fiber f (Ne.symm hwz), smul_zero]
  · intro hznot
    exact (hznot hz).elim
end PVM
