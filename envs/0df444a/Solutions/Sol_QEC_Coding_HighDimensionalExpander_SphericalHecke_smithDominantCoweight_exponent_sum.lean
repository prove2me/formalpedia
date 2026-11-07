-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDominantCoweight_exponent_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:55.013831+00:00
-- url     : https://prove2.me/submissions/e8c26af7-8ebb-456a-92a0-85fd96bdfb3e

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
    (∑ i, ((smithDominantCoweight A).exponent i : ℤ)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by
  simpa [smithDominantCoweight, dominantSort, Function.comp_def] using
    (Equiv.sum_comp
      (dominantSortPermutation
        (smithExponent (k := k) (d := d) A))
      (fun i => (smithExponent (k := k) (d := d) A i : ℤ)))
end QEC.Coding.HighDimensionalExpander.SphericalHecke
