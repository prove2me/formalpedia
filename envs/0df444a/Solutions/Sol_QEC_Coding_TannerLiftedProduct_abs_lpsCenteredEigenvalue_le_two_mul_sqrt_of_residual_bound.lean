-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:23:02.966089+00:00
-- url     : https://prove2.me/submissions/4f630336-95ce-49f5-9939-41a9d86febda

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (hBound : HasOptimalCenteredThetaCoefficientBound a)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) := by
  obtain ⟨C, hC, hResidual⟩ := hBound
  apply abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
  intro t ht
  exact lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
    a C hC hResidual i t ht
end QEC.Coding.TannerLiftedProduct
