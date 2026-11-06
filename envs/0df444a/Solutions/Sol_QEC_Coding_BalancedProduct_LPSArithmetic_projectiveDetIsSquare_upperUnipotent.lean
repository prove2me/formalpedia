-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_upperUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:52:59.770038+00:00
-- url     : https://prove2.me/submissions/6bf14ab5-a888-428a-8d02-408af571a107

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_mk_iff

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution (x : R) :
    ProjectiveDetIsSquare (upperUnipotentPGL x) := by
  rw [upperUnipotentPGL_apply, projectiveDetIsSquare_mk_iff]
  have hdet :
      (Matrix.GeneralLinearGroup.upperRightHom x).det = (1 : Rˣ) := by
    ext
    simp [Matrix.GeneralLinearGroup.det,
      Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.det_fin_two_of]
  rw [hdet]
  exact IsSquare.one
end QEC.Coding.BalancedProduct.LPSArithmetic
