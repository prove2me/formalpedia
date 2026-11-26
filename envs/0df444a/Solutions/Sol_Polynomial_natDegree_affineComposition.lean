-- Prove2me | solution 1 for Polynomial.natDegree_affineComposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:59.745817+00:00
-- url     : https://prove2.me/submissions/e838360d-2c5d-4701-a56b-9879e23d43cb

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_Polynomial_aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] Polynomial.aeval_affineComposition

set_option autoImplicit false
open scoped Polynomial
open Polynomial
namespace Polynomial
theorem _root_.solution (p : ℂ[X]) {a b : ℂ} (ha : a ≠ 0) :
    (affineComposition p a b).natDegree = p.natDegree := by
  rw [affineComposition, natDegree_comp]
  have hdeg : (C a * X + C b).natDegree = 1 := by
    simp only [natDegree_add_C, ne_eq, map_eq_zero, ha, not_false_eq_true, natDegree_mul_X,
      natDegree_C, zero_add]
  rw [hdeg, Nat.mul_one]
end Polynomial
