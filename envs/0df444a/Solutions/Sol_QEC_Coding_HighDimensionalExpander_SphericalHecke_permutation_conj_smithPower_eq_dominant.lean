-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPower_eq_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:18.141664+00:00
-- url     : https://prove2.me/submissions/50bd8ce9-b1b7-4761-894a-3f5f7942a4e0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationGeneralLinear_conj_diagonal

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
    permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
        (permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantGeneralLinear k (smithDominantCoweight A) := by
  change
    permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        diagonalGeneralLinear (LocalFunctionField k) d
          (fun i => uniformizerUnit k ^
            smithExponent (k := k) (d := d) A i) *
        (permutationGeneralLinear (LocalFunctionField k)
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      diagonalGeneralLinear (LocalFunctionField k) d
        (fun i => uniformizerUnit k ^
          dominantSort (smithExponent (k := k) (d := d) A) i)
  rw [permutationGeneralLinear_conj_diagonal]
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
