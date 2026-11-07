-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationGeneralLinear_conj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:41:21.344179+00:00
-- url     : https://prove2.me/submissions/f973ef90-f076-4b26-8628-cc52c030bc50

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
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (v : Fin d → Units R) :
    permutationGeneralLinear R σ * diagonalGeneralLinear R d v *
        (permutationGeneralLinear R σ)⁻¹ =
      diagonalGeneralLinear R d (v ∘ σ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  classical
  simp [permutationGeneralLinear, diagonalGeneralLinear_apply,
    Matrix.mul_apply, Function.comp_def, Equiv.Perm.permMatrix,
    PEquiv.toMatrix]
  rw [Finset.sum_eq_single (σ i)]
  · simp
  · intro b _ hne
    have hib : σ i ≠ b := fun h => hne h.symm
    simp [hib]
  · simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
