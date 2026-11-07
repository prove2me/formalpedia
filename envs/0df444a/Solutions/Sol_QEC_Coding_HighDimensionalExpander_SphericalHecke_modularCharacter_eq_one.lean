-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:17.937117+00:00
-- url     : https://prove2.me/submissions/7bd1427d-0d92-42ee-b406-47e281f31de8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_eq_localCartanFactors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithLeft_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithRight_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_eq_one_of_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_smithPowerCoweight_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (g : PGL(Fin d, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  let left : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A)
  let right : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithRightGeneralLinearLocal (k := k) (d := d) A)
  have hleft :
      MeasureTheory.Measure.modularCharacter left = 1 :=
    modularCharacter_eq_one_of_mem_maximalCompact
      left
      (smithLeft_mem_maximalCompact (k := k) (d := d) A)
  have hright_inv :
      MeasureTheory.Measure.modularCharacter right⁻¹ = 1 :=
    modularCharacter_eq_one_of_mem_maximalCompact
      right⁻¹
      ((maximalCompact k d).inv_mem
        (smithRight_mem_maximalCompact (k := k) (d := d) A))
  have hsmith :
      MeasureTheory.Measure.modularCharacter
        (smithPowerCoweight (k := k) (d := d) A) = 1 :=
    modularCharacter_smithPowerCoweight_eq_one hd A
  rw [projective_eq_localCartanFactors A]
  change MeasureTheory.Measure.modularCharacter
    (left * smithPowerCoweight (k := k) (d := d) A * right⁻¹) = 1
  simp only [map_mul, hleft, hsmith, hright_inv, mul_one]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
