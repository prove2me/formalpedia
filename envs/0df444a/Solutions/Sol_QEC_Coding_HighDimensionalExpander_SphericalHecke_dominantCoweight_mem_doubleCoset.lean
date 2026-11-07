-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:47:43.30925+00:00
-- url     : https://prove2.me/submissions/2ccfbade-d72d-49a3-a4f4-7df1425357b7

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    dominantCoweight k weight ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset, Set.mem_mul]
  refine ⟨dominantCoweight k weight, ?_, 1, (maximalCompact k d).one_mem,
    mul_one _⟩
  rw [Set.mem_mul]
  exact ⟨1, (maximalCompact k d).one_mem, dominantCoweight k weight,
    Set.mem_singleton _, one_mul _⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
