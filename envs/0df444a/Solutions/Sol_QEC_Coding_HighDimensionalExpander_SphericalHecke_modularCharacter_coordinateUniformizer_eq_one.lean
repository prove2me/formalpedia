-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:22.704195+00:00
-- url     : https://prove2.me/submissions/3877f912-fc1c-45bd-b56f-926b213e7017

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerCoweight
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_coordinateUniformizer_eq
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
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) (i : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) = 1 := by
  let δ : PGL(Fin d, LocalFunctionField k) →* NNReal :=
    MeasureTheory.Measure.modularCharacter
  have hprod :
      ((List.finRange d).map
        (fun j => δ (coordinateUniformizerCoweight k d j))).prod = 1 := by
    calc
      ((List.finRange d).map
          (fun j => δ (coordinateUniformizerCoweight k d j))).prod =
          δ (((List.finRange d).map
            (coordinateUniformizerCoweight k d)).prod) := by
        exact List.prod_map_hom (List.finRange d)
          (coordinateUniformizerCoweight k d) δ
      _ = δ 1 := congrArg δ (prod_coordinateUniformizerCoweight k d)
      _ = 1 := map_one δ
  have hconstant :
      (fun j : Fin d => δ (coordinateUniformizerCoweight k d j)) =
        (fun _ : Fin d => δ (coordinateUniformizerCoweight k d i)) := by
    funext j
    exact modularCharacter_coordinateUniformizer_eq k j i
  rw [hconstant] at hprod
  have hpow :
      (δ (coordinateUniformizerCoweight k d i)) ^ d = 1 := by
    simpa using hprod
  exact (pow_eq_one_iff_of_nonneg (by positivity) (Nat.ne_of_gt hd)).mp hpow
end QEC.Coding.HighDimensionalExpander.SphericalHecke
