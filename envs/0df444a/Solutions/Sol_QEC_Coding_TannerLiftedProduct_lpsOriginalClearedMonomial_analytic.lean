-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:05.491133+00:00
-- url     : https://prove2.me/submissions/a5025511-cdd4-4073-b994-951aabe98bab

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    AnalyticAt ℂ (lpsOriginalClearedMonomial N B i k) 0 := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 := by
    exact lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  exact ((lpsOriginalPower_analytic _).mul (lpsOriginalJQCoefficient_analytic_zero.pow i)).mul (hKN.pow k)
end QEC.Coding.TannerLiftedProduct
