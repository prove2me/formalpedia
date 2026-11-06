-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:52:55.834332+00:00
-- url     : https://prove2.me/submissions/2dbc7559-7072-40ee-9ec2-687893cb38dd

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_val

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hq : legendreSym q p = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  apply not_projectiveDetIsSquare_mk_of_val A
  rw [hdet]
  exact (legendreSym.eq_neg_one_iff' (p := q) (a := p)).mp hq
end QEC.Coding.BalancedProduct.LPSArithmetic
