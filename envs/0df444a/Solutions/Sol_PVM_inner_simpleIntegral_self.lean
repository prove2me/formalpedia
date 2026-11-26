-- Prove2me | solution 1 for PVM.inner_simpleIntegral_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:21.405906+00:00
-- url     : https://prove2.me/submissions/c449a8f5-2745-485c-9a01-754774333896

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) (x : E) :
    @inner ℂ E _ x (E_pvm.simpleIntegral f x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by
  rw [PVM.simpleIntegral, sum_apply, inner_sum]
  have hfint : Integrable f (E_pvm.scalarMeasure x) := by
    apply Integrable.of_bound f.measurable.aestronglyMeasurable
      (∑ z ∈ f.range, ‖z‖)
    apply ae_of_all
    intro t
    exact Finset.single_le_sum
      (fun z _hz => norm_nonneg z) (f.mem_range_self t)
  rw [SimpleFunc.integral_eq_sum f hfint]
  apply Finset.sum_congr rfl
  intro z hz
  rw [smul_apply, inner_smul_right]
  have hreal : (E_pvm.scalarMeasure x).real (f ⁻¹' {z}) =
      E_pvm.scalarContent x (f ⁻¹' {z}) := by
    rw [measureReal_def,
      E_pvm.scalarMeasure_apply x (f ⁻¹' {z}) (f.measurableSet_fiber z),
      ENNReal.toReal_ofReal
        (E_pvm.scalarContent_nonneg x (f ⁻¹' {z}) (f.measurableSet_fiber z))]
  rw [hreal]
  change z * (@inner ℂ E _ x (E_pvm.proj (f ⁻¹' {z}) x)) =
      (E_pvm.scalarContent x (f ⁻¹' {z})) • z
  rw [show @inner ℂ E _ x (E_pvm.proj (f ⁻¹' {z}) x) =
      E_pvm.scalarContent x (f ⁻¹' {z}) by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,
      (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
        (f.measurableSet_fiber z)).1]
    change @inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x =
      (((@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re : ℝ) : ℂ)
    have hpos : ContinuousLinearMap.IsPositive
        (E_pvm.proj (f ⁻¹' {z})) :=
      (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
          (f.measurableSet_fiber z)).2).mpr
          (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
            (f.measurableSet_fiber z)).1
    exact ((LinearMap.isPositive_iff_complex _).mp hpos.toLinearMap x).1.symm]
  change z * (E_pvm.scalarContent x (f ⁻¹' {z}) : ℂ) =
    (E_pvm.scalarContent x (f ⁻¹' {z}) : ℂ) * z
  exact mul_comm _ _
end PVM
