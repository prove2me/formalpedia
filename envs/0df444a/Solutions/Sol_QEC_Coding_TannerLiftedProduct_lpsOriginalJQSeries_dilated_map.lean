-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_dilated_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:21:37.592006+00:00
-- url     : https://prove2.me/submissions/a3eb343c-60d4-4cdb-b29d-ae56ba90aca5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_map


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : N≠0) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.expand N hN lpsOriginalJQSeries)=
      lpsOriginalTaylorSeries (fun q=>lpsOriginalJQCoefficient (q^N)) := by
  rw [PowerSeries.map_expand,lpsOriginalJQSeries_map]
  exact (lpsOriginalTaylorSeries_comp_pow lpsOriginalJQCoefficient_analytic_zero N hN).symm
end QEC.Coding.TannerLiftedProduct
