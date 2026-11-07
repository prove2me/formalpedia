-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_normalizedDominantGeneralLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:29.968511+00:00
-- url     : https://prove2.me/submissions/06a9c403-9fac-466d-9d01-8fead44a5141

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
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
        (uniformizerUnit k ^ weight.exponent (Fin.last n)) *
      dominantGeneralLinear k (normalizeDominantCoweight weight).toDominant =
        dominantGeneralLinear k weight := by
  let Φ := diagonalGeneralLinearHom (LocalFunctionField k) (n + 1)
  have hscalar_base :
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k) =
        Φ (fun _ : Fin (n + 1) ↦ uniformizerUnit k) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Φ, diagonalGeneralLinearHom, Matrix.diagonal_apply]
  have hscalar :
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k ^ weight.exponent (Fin.last n)) =
        Φ (fun _ : Fin (n + 1) ↦
          uniformizerUnit k ^ weight.exponent (Fin.last n)) := by
    calc
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
          (uniformizerUnit k ^ weight.exponent (Fin.last n)) =
          (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
            (uniformizerUnit k)) ^ weight.exponent (Fin.last n) := by
            rw [map_pow]
      _ = (Φ (fun _ : Fin (n + 1) ↦ uniformizerUnit k)) ^
          weight.exponent (Fin.last n) := by rw [hscalar_base]
      _ = Φ ((fun _ : Fin (n + 1) ↦ uniformizerUnit k) ^
          weight.exponent (Fin.last n)) := by rw [map_pow]
      _ = Φ (fun _ : Fin (n + 1) ↦
          uniformizerUnit k ^ weight.exponent (Fin.last n)) := by
            congr 1
  rw [hscalar]
  change Φ (fun _ : Fin (n + 1) ↦
      uniformizerUnit k ^ weight.exponent (Fin.last n)) *
    Φ (fun i ↦ uniformizerUnit k ^
      (weight.exponent i - weight.exponent (Fin.last n))) =
    Φ (fun i ↦ uniformizerUnit k ^ weight.exponent i)
  rw [← map_mul]
  congr 1
  funext i
  have hlast : weight.exponent (Fin.last n) ≤ weight.exponent i :=
    weight.antitone_exponent (Fin.le_last i)
  change uniformizerUnit k ^ weight.exponent (Fin.last n) *
      uniformizerUnit k ^
        (weight.exponent i - weight.exponent (Fin.last n)) =
    uniformizerUnit k ^ weight.exponent i
  rw [← pow_add, Nat.add_comm,
    Nat.sub_add_cancel hlast]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
