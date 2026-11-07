-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:27:31.132196+00:00
-- url     : https://prove2.me/submissions/e4d809aa-29d3-4442-a3f7-c760e05dd578

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    AnalyticAt ℂ (lpsOriginalClearedUnivariateCusp N D p) 0 := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  exact (Finset.range (D+1)).analyticAt_sum fun i _ =>
    (analyticAt_const.mul (lpsOriginalPower_analytic _)).mul (hKN.pow i)
end QEC.Coding.TannerLiftedProduct
