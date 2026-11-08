-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:10:04.878373+00:00
-- url     : https://prove2.me/submissions/98d9f196-5e8e-4d5f-adcc-bdd9364805f3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (h : ∀ t : ℝ, Real.sqrt (p : ℝ) < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
        =O[atTop] fun n : ℕ => t ^ (2 * n)) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) :=
  abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    (Nat.cast_pos.mpr a.degreePrime.pos) _ h
end QEC.Coding.TannerLiftedProduct
