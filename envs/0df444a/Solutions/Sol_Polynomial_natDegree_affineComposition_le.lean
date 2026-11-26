-- Prove2me | solution 1 for Polynomial.natDegree_affineComposition_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:55.372955+00:00
-- url     : https://prove2.me/submissions/70fd1218-9bc0-46b1-a931-fa6792e3766f

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
theorem _root_.solution (p : ℂ[X]) (a b : ℂ) :
    (affineComposition p a b).natDegree ≤ p.natDegree := by
  rw [affineComposition]
  have hq : (C a * X + C b).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [pow_one] using natDegree_C_mul_X_pow_le a 1
  calc
    (p.comp (C a * X + C b)).natDegree
        ≤ p.natDegree * (C a * X + C b).natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hq
    _ = p.natDegree := Nat.mul_one _
end Polynomial
