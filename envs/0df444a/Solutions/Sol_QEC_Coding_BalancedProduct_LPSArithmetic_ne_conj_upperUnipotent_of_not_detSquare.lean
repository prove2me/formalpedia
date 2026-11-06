-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.ne_conj_upperUnipotent_of_not_detSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:54:08.514922+00:00
-- url     : https://prove2.me/submissions/1b3c3308-f4ec-4b17-9032-980b254468da

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_upperUnipotent
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_conj_iff

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    {s : PGL(2, R)}
    (hs : ¬ ProjectiveDetIsSquare s)
    (g : PGL(2, R)) (x : R) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ := by
  intro heq
  apply hs
  rw [heq, projectiveDetIsSquare_conj_iff]
  exact projectiveDetIsSquare_upperUnipotent x
end QEC.Coding.BalancedProduct.LPSArithmetic
