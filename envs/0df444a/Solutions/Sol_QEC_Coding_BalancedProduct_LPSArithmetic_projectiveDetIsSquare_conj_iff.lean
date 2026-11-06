-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:01.897188+00:00
-- url     : https://prove2.me/submissions/c19360ad-ca75-4453-a23b-8c61ffe99a35

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
    (g h : PGL(2, R)) :
    ProjectiveDetIsSquare (g * h * g⁻¹) ↔ ProjectiveDetIsSquare h := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk G =>
      induction h using Matrix.ProjGenLinGroup.induction_on with
      | mk H =>
          simp only [← map_mul, ← map_inv]
          rw [projectiveDetIsSquare_mk_iff, projectiveDetIsSquare_mk_iff]
          simp
end QEC.Coding.BalancedProduct.LPSArithmetic
