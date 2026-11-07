-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:04.903345+00:00
-- url     : https://prove2.me/submissions/7559ca62-1e97-4e15-9f48-e2535f81066b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
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
        coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerGeneralLinearLocal (k := k) (d := d) A := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) d
  have htuple :
      ((List.finRange d).map (fun i =>
        coordinateUniformizerUnits k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        (fun j => uniformizerUnit k ^
          smithExponent (k := k) (d := d) A j) := by
    funext j
    rw [Pi.list_prod_apply, List.map_map]
    change ((List.finRange d).map (fun i : Fin d =>
      (if j = i then uniformizerUnit k else 1) ^
        smithExponent (k := k) (d := d) A i)).prod = _
    rw [← List.ofFn_eq_map, List.prod_ofFn]
    simp
  calc
    ((List.finRange d).map (fun i =>
        coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
        ((List.finRange d).map (fun i =>
          Φ (coordinateUniformizerUnits k d i ^
            smithExponent (k := k) (d := d) A i))).prod := by
      congr 1
      apply List.map_congr_left
      intro i _
      rw [map_pow]
      rfl
    _ = Φ (((List.finRange d).map (fun i =>
          coordinateUniformizerUnits k d i ^
            smithExponent (k := k) (d := d) A i)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (fun i => coordinateUniformizerUnits k d i ^
          smithExponent (k := k) (d := d) A i) Φ
    _ = Φ (fun j => uniformizerUnit k ^
          smithExponent (k := k) (d := d) A j) := congrArg Φ htuple
    _ = smithPowerGeneralLinearLocal (k := k) (d := d) A := rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
