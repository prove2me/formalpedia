-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight_pow_eq_smithPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:46.198884+00:00
-- url     : https://prove2.me/submissions/d2818895-1979-4962-8ea2-bf5cdffb554c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
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
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerCoweight (k := k) (d := d) A := by
  calc
    ((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        ((List.finRange d).map (fun i =>
          Matrix.ProjGenLinGroup.mk
            (coordinateUniformizerGeneralLinear k d i ^
              smithExponent (k := k) (d := d) A i))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      simp [coordinateUniformizerCoweight]
    _ = Matrix.ProjGenLinGroup.mk
        (((List.finRange d).map (fun i =>
          coordinateUniformizerGeneralLinear k d i ^
            smithExponent (k := k) (d := d) A i)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)
        Matrix.ProjGenLinGroup.mk
    _ = smithPowerCoweight (k := k) (d := d) A := by
      rw [prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower]
      rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
