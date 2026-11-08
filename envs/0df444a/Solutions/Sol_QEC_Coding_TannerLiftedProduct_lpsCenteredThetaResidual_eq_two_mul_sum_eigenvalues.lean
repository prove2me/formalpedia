-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:50:58.418197+00:00
-- url     : https://prove2.me/submissions/1594d3c4-e098-47ec-84d8-b6e0cbf3d737

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a n =
      2 * (∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)) := by
  exact (two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
    a n).symm
end QEC.Coding.TannerLiftedProduct
