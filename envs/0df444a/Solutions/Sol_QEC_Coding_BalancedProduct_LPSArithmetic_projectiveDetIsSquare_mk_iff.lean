-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:49:37.746829+00:00
-- url     : https://prove2.me/submissions/18111244-e0c3-4476-9630-182289af32cf

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_det_isSquare_iff_of_projective_eq

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution (A : GL (Fin 2) R) :
    ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) ↔ IsSquare A.det := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    exact (det_isSquare_iff_of_projective_eq hBA).mp hB
  · intro hA
    exact ⟨A, rfl, hA⟩
end QEC.Coding.BalancedProduct.LPSArithmetic
