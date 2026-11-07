-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.permutationCoweight_mem_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:38.034942+00:00
-- url     : https://prove2.me/submissions/98172106-8511-4d9d-8682-0074e5d10de5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToLocal_permutation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permutationCoweight k σ ∈ maximalCompact k d := by
  rw [permutationCoweight,
    ← powerSeriesGeneralLinearToLocal_permutation k σ]
  exact mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    (permutationGeneralLinear (IntegerRing k) σ)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
