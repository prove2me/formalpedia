-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsComplexVerticalNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:03.959376+00:00
-- url     : https://prove2.me/submissions/fe022295-a594-41ef-b55e-e18aa7176d68

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : ℝ) :
    (volume : Measure ℂ) {z : ℂ | z.re = x} = 0 := by
  have h := Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) (0 : Fin 2) x
  have hm : MeasurableSet {f : Fin 2 → ℝ | f 0 = x} :=
    measurableSet_eq_fun (measurable_pi_apply (0 : Fin 2)) measurable_const
  have he := Complex.volume_preserving_equiv_pi.measure_preimage hm.nullMeasurableSet
  change (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' {f : Fin 2 → ℝ | f 0 = x}) = 0
  exact he.trans h
end QEC.Coding.TannerLiftedProduct
