-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:51:16.572622+00:00
-- url     : https://prove2.me/submissions/ec5b0427-a5a4-41c0-b4ea-56020c2a959e

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
theorem _root_.solution
    (A : GL (Fin 2) R)
    (hA : ¬ IsSquare (A.det : R)) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  rw [projectiveDetIsSquare_mk_iff]
  rintro ⟨u, hu⟩
  apply hA
  exact ⟨(u : R), congrArg Units.val hu⟩
end QEC.Coding.BalancedProduct.LPSArithmetic
