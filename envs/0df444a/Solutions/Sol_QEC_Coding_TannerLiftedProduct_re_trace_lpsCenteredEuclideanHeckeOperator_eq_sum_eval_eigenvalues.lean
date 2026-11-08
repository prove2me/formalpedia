-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:05:17.15828+00:00
-- url     : https://prove2.me/submissions/01eadfc3-4265-46d9-80a9-ff0c6e9aa27a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_re_eval_lpsHeckePolynomial_complex_ofReal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
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
    Complex.re (LinearMap.trace ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n)) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) := by
  rw [trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact re_eval_lpsHeckePolynomial_complex_ofReal _ _
end QEC.Coding.TannerLiftedProduct
