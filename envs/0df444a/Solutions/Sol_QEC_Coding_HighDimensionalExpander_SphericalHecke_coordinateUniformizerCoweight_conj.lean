-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:49.178095+00:00
-- url     : https://prove2.me/submissions/7344871a-4d12-4e77-a883-cfe4b757ae06

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerGeneralLinear_conj

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationCoweight k (Equiv.swap i j) *
        coordinateUniformizerCoweight k d i *
        (permutationCoweight k (Equiv.swap i j))⁻¹ =
      coordinateUniformizerCoweight k d j := by
  exact congrArg Matrix.ProjGenLinGroup.mk
      (coordinateUniformizerGeneralLinear_conj k i j)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
