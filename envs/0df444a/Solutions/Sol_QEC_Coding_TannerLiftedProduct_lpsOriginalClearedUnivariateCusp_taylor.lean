-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:27:42.163479+00:00
-- url     : https://prove2.me/submissions/bb5aab0e-561a-4f53-9c96-10c4f011061c

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedUnivariateCusp N D p)=
      lpsOriginalClearedUnivariateSeries N D
        (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))) p := by
  classical
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  rw [lpsOriginalClearedUnivariateCusp,lpsOriginalTaylorSeries_sum
    (Finset.range (D+1))
    (fun i=>fun q : ℂ=>p.coeff i*q^(N*(D-i))*lpsOriginalJQCoefficient (q^N)^i)
    (fun i _ => (analyticAt_const.mul (lpsOriginalPower_analytic _)).mul (hKN.pow i))]
  unfold lpsOriginalClearedUnivariateSeries
  apply Finset.sum_congr rfl
  intro i _hi
  change lpsOriginalTaylorSeries
    ((fun q : ℂ=>p.coeff i*q^(N*(D-i))) *
      ((fun q : ℂ=>lpsOriginalJQCoefficient (q^N))^i))=_
  have hf : AnalyticAt ℂ (fun q : ℂ=>p.coeff i*q^(N*(D-i))) 0 :=
    analyticAt_const.mul (lpsOriginalPower_analytic _)
  rw [lpsOriginalTaylorSeries_mul hf
      (hKN.pow i),lpsOriginalTaylorSeries_const_mul,lpsOriginalTaylorSeries_qpow,
      lpsOriginalTaylorSeries_pow hKN]
end QEC.Coding.TannerLiftedProduct
