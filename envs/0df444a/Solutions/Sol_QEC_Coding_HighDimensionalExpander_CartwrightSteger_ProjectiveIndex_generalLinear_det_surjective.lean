-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generalLinear_det_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:36:19.665695+00:00
-- url     : https://prove2.me/submissions/78118e6f-0076-470e-b875-1746083a3711

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
omit [Fintype K]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution :
    Function.Surjective
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup n K →* Kˣ) := by
  intro u
  let i0 : n := Classical.choice (inferInstance : Nonempty n)
  let f : n → K := fun i => if i = i0 then (u : K) else 1
  let fInv : n → K := fun i => if i = i0 then (u⁻¹ : Kˣ) else 1
  let fu : (n → K)ˣ :=
    { val := f
      inv := fInv
      val_inv := by
        funext i
        by_cases hi : i = i0 <;> simp [f, fInv, hi]
      inv_val := by
        funext i
        by_cases hi : i = i0 <;> simp [f, fInv, hi] }
  let A : Matrix.GeneralLinearGroup n K :=
    Units.map (Matrix.diagonalRingHom n K).toMonoidHom fu
  refine ⟨A, ?_⟩
  apply Units.ext
  change Matrix.det (Matrix.diagonal f) = (u : K)
  rw [Matrix.det_diagonal]
  classical
  simp [f, i0]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
