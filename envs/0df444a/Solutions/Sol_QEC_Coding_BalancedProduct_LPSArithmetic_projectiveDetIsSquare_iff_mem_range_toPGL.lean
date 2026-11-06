-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_iff_mem_range_toPGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:57.514023+00:00
-- url     : https://prove2.me/submissions/2262f031-e7ae-4e85-86bf-8bfb58189909

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
    (g : PGL(2, R)) :
    ProjectiveDetIsSquare g ↔
      g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := R)).range := by
  constructor
  · rintro ⟨A, hAg, ⟨k, hk⟩⟩
    let r : Rˣ := k⁻¹
    have hr : r ^ 2 * A.det = 1 := by
      rw [hk]
      simp [r, pow_two]
    have hrMatrix : Matrix.det (r.1 • A.1) = 1 := by
      simpa [Matrix.det_smul] using congrArg Units.val hr
    let X : SL(2, R) := ⟨r.1 • A.1, hrMatrix⟩
    refine ⟨(QuotientGroup.mk X : PSL(2, R)), ?_⟩
    change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (QuotientGroup.mk X : PSL(2, R)) = g
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    calc
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X) =
          Matrix.ProjGenLinGroup.mk A := by
        rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
        refine ⟨r⁻¹, ?_⟩
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [X, r, Matrix.SpecialLinearGroup.toGL, Matrix.mul_apply,
            mul_comm, mul_assoc]
      _ = g := hAg
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H X =>
        rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
          projectiveDetIsSquare_mk_iff]
        simp
end QEC.Coding.BalancedProduct.LPSArithmetic
