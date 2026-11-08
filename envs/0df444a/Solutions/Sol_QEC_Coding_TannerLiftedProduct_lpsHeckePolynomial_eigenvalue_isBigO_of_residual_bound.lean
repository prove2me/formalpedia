-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:20:20.700992+00:00
-- url     : https://prove2.me/submissions/ccaa5873-5fce-4e63-ab45-caaa46b87180

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (C : ℝ) (hC : 0 ≤ C)
    (hResidual : ∀ n : ℕ,
      |lpsCenteredThetaResidual a (2 * n)| ≤
        C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n))
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (t : ℝ) (ht : Real.sqrt (p : ℝ) < t) :
    (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ => t ^ (2 * n) :=
  lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
    a (p : ℝ) le_rfl C hC hResidual i t ht
end QEC.Coding.TannerLiftedProduct
