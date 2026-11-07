-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_dominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:09:15.458097+00:00
-- url     : https://prove2.me/submissions/ddc8cfe9-7354-4b01-89df-2d3531f3f605

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_mem_dominantDoubleCoset

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {d : ℕ}
    (g : PGL(Fin d, LocalFunctionField k)) :
    ∃ weight : DominantCoweight d, g ∈ dominantDoubleCoset k weight := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  exact ⟨smithDominantCoweight A, mk_mem_dominantDoubleCoset A⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
