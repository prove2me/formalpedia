-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det_401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:54:05.592108+00:00
-- url     : https://prove2.me/submissions/f894fbd5-b7b2-49f6-b185-1708532c990d

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_det

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    {q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (401 : ZMod q))
    (hq : legendreSym q 401 = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  exact not_projectiveDetIsSquare_mk_of_det A hdet hq
end QEC.Coding.BalancedProduct.LPSArithmetic
