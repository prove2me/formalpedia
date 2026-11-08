-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:08:10.373406+00:00
-- url     : https://prove2.me/submissions/996654ad-d87a-46d0-a5c5-b5d6b5adc2c0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    2 * (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      lpsCenteredThetaResidual a (2 * n) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  exact two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
    a n i
end QEC.Coding.TannerLiftedProduct
