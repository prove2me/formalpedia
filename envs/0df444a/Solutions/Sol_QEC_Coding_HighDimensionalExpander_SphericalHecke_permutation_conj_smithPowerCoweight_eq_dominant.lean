-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.permutation_conj_smithPowerCoweight_eq_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:22.362413+00:00
-- url     : https://prove2.me/submissions/696354a0-063f-4698-8002-0823d9234fd2

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutation_conj_smithPower_eq_dominant
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
    permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)) *
        smithPowerCoweight (k := k) (d := d) A *
        (permutationCoweight k
          (dominantSortPermutation
            (smithExponent (k := k) (d := d) A)))⁻¹ =
      dominantCoweight k (smithDominantCoweight A) := by
  simpa [permutationCoweight, smithPowerCoweight, dominantCoweight] using
    congrArg Matrix.ProjGenLinGroup.mk
      (permutation_conj_smithPower_eq_dominant A)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
