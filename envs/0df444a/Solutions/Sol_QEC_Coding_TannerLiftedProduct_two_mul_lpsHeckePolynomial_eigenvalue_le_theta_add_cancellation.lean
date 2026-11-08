-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:01.448748+00:00
-- url     : https://prove2.me/submissions/d83f95f0-3fe2-4469-94fc-d85319657c07

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
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
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ (2 * n))
            (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ j ∈ Finset.range (2 * n + 1), (p : ℝ) ^ j) -
          (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval 0) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  have hTerm := lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
    a n i
  have hTrace :=
    two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
      a (2 * n)
  linarith
end QEC.Coding.TannerLiftedProduct
