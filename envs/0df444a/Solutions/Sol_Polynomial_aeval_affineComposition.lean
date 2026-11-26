-- Prove2me | solution 1 for Polynomial.aeval_affineComposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:55:02.02138+00:00
-- url     : https://prove2.me/submissions/d2cbeb2f-a0ad-424a-bf1c-268287a2a18e

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Theorems.Thm_Polynomial_eval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition

set_option autoImplicit false
open scoped Polynomial
open Polynomial
namespace Polynomial
theorem _root_.solution {A : Type*} [Semiring A] [Algebra ℂ A]
    (p : ℂ[X]) (a b : ℂ) (x : A) :
    aeval x (affineComposition p a b) = aeval (a • x + b • (1 : A)) p := by
  simp only [affineComposition, aeval_comp, map_add, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, aeval_X, Algebra.smul_mul_assoc, one_mul]
end Polynomial
