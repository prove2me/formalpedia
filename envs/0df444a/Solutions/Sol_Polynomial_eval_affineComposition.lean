-- Prove2me | solution 1 for Polynomial.eval_affineComposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:21.651922+00:00
-- url     : https://prove2.me/submissions/9c2ed95a-f925-4e63-b85d-195c726c7af9

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial

set_option autoImplicit false
open scoped Polynomial
open Polynomial
namespace Polynomial
theorem _root_.solution (p : ℂ[X]) (a b z : ℂ) :
    (affineComposition p a b).eval z = p.eval (a * z + b) := by
  simp only [affineComposition, eval_comp, eval_add, eval_mul, eval_C, eval_X]
end Polynomial
