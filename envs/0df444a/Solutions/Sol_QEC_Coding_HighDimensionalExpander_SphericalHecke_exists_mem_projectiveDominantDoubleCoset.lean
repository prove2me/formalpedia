-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_mem_projectiveDominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:10:00.524992+00:00
-- url     : https://prove2.me/submissions/c4b07aec-7fe6-421e-8deb-0663e9faa0b0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_normalize
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_dominantDoubleCoset

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {n : ℕ}
    (g : PGL(Fin (n + 1), LocalFunctionField k)) :
    ∃ weight : ProjectiveDominantCoweight n,
      g ∈ projectiveDominantDoubleCoset k weight := by
  obtain ⟨weight, hg⟩ := exists_mem_dominantDoubleCoset k g
  refine ⟨normalizeDominantCoweight weight, ?_⟩
  rw [projectiveDominantDoubleCoset,
    dominantDoubleCoset_normalize]
  exact hg
end QEC.Coding.HighDimensionalExpander.SphericalHecke
