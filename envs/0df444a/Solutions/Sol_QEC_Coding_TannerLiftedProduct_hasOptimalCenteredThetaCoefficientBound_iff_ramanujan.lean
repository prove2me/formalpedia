-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_iff_ramanujan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:36.829702+00:00
-- url     : https://prove2.me/submissions/dd1d8f5d-f1ec-4dae-af46-b3e1a3b9787a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasOptimalCenteredThetaCoefficientBound_of_ramanujan
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) :
    HasOptimalCenteredThetaCoefficientBound a ↔
      ∀ i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
          2 * Real.sqrt (p : ℝ) := by
  constructor
  · intro h i
    exact abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound a h i
  · exact hasOptimalCenteredThetaCoefficientBound_of_ramanujan a
end QEC.Coding.TannerLiftedProduct
