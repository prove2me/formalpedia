-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:54.930185+00:00
-- url     : https://prove2.me/submissions/6f936042-e1f4-4cdc-bf3a-facf7fca8aec

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
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerGeneralLinear k d)).prod =
      Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k) := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) d
  have htuple :
      ((List.finRange d).map (coordinateUniformizerUnits k d)).prod =
        (fun _ : Fin d => uniformizerUnit k) := by
    funext j
    rw [Pi.list_prod_apply]
    rw [List.map_map]
    change ((List.finRange d).map
      (fun i : Fin d => if j = i then uniformizerUnit k else 1)).prod = _
    rw [← List.ofFn_eq_map, List.prod_ofFn]
    simp
  calc
    ((List.finRange d).map
        (coordinateUniformizerGeneralLinear k d)).prod =
        Φ ((List.finRange d).map
          (coordinateUniformizerUnits k d)).prod := by
      exact List.prod_map_hom (List.finRange d)
        (coordinateUniformizerUnits k d) Φ
    _ = Φ (fun _ : Fin d => uniformizerUnit k) := congrArg Φ htuple
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [Φ, diagonalGeneralLinearHom, Matrix.diagonal_apply]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
