-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:02:29.224664+00:00
-- url     : https://prove2.me/submissions/7ecf18c2-6c23-4af8-b1e3-da7c4e8b6459

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_aeval_eq_sum_eval_eigenvalues


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℂ (p : ℂ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i : ℂ) := by
  unfold lpsCenteredEuclideanHeckeOperator
  exact trace_aeval_eq_sum_eval_eigenvalues _
    (lpsCenteredAdjacencyEuclidean_isSymmetric a) _
end QEC.Coding.TannerLiftedProduct
