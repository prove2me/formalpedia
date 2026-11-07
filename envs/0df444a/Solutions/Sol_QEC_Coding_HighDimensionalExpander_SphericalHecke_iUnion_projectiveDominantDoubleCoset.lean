-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.iUnion_projectiveDominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:11:27.059973+00:00
-- url     : https://prove2.me/submissions/15b26ec0-1ea0-4cd7-b826-1dd097d48649

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_projectiveDominantDoubleCoset

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {n : ℕ} :
    ⋃ weight : ProjectiveDominantCoweight n,
      projectiveDominantDoubleCoset k weight = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨weight, hg⟩ :=
    exists_mem_projectiveDominantDoubleCoset k g
  exact Set.mem_iUnion.2 ⟨weight, hg⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
