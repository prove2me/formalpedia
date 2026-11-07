-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_rankThree_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:58:55.086969+00:00
-- url     : https://prove2.me/submissions/9a032712-0532-40a4-af70-dbbb163733ea

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k]
    {a b : ProjectiveDominantCoweight 2} (hab : a ≠ b) :
    Disjoint (projectiveDominantDoubleCoset k a)
      (projectiveDominantDoubleCoset k b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
    k a b ⟨x, hxa, hxb⟩)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
