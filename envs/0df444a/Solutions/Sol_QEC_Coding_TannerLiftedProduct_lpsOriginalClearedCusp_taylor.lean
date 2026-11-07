-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:25:51.609368+00:00
-- url     : https://prove2.me/submissions/73d9a6d9-74a6-43f5-a9e0-6a7ec95d1600

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_taylor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp N B P)=
      ∑ k∈P.support,∑ i∈(P.coeff k).support,
        PowerSeries.C ((P.coeff k).coeff i)*
          PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by
  classical
  unfold lpsOriginalClearedCusp
  rw [lpsOriginalTaylorSeries_sum P.support (fun k=>∑ i∈(P.coeff k).support,fun q=>(P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q) (fun k _=>
    (P.coeff k).support.analyticAt_sum fun i _=>analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lpsOriginalTaylorSeries_sum (P.coeff k).support (fun i=>fun q=>(P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q) (fun i _=>analyticAt_const.mul
    (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalTaylorSeries_const_mul,lpsOriginalClearedMonomial_taylor N hN]
end QEC.Coding.TannerLiftedProduct
