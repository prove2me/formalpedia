-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.right_mul_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:45.744219+00:00
-- url     : https://prove2.me/submissions/28404cfe-cfd4-43c3-819b-f8410ad868a0

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    (g : PGL(2, R)) (h : upperUnipotentSubgroup (R := R)) :
    g * (h : PGL(2, R)) = g ↔ h = 1 := by
  constructor
  · intro hfix
    apply Subtype.ext
    have heq : g * (h : PGL(2, R)) = g * 1 := by simpa using hfix
    exact mul_left_cancel heq
  · rintro rfl
    simp
end QEC.Coding.BalancedProduct.LPSArithmetic
