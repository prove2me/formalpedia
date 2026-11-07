-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_smithPowerCoweight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:05.555857+00:00
-- url     : https://prove2.me/submissions/1af66650-dbcc-4572-86d0-46926b65e925

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_coordinateUniformizer_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerCoweight_pow_eq_smithPower
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
    {k : Type u} [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (A : GL (Fin d) (LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter
        (smithPowerCoweight (k := k) (d := d) A) = 1 := by
  let δ : PGL(Fin d, LocalFunctionField k) →* NNReal :=
    MeasureTheory.Measure.modularCharacter
  rw [← prod_coordinateUniformizerCoweight_pow_eq_smithPower A]
  change δ (((List.finRange d).map (fun i =>
    coordinateUniformizerCoweight k d i ^
      smithExponent (k := k) (d := d) A i)).prod) = 1
  calc
    δ (((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod) =
        ((List.finRange d).map (fun i =>
          δ (coordinateUniformizerCoweight k d i ^
            smithExponent (k := k) (d := d) A i))).prod := by
      exact (List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i) δ).symm
    _ = 1 := by
      simp only [map_pow]
      have hone (i : Fin d) :
          δ (coordinateUniformizerCoweight k d i) = 1 :=
        modularCharacter_coordinateUniformizer_eq_one k hd i
      simp_rw [hone]
      simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
