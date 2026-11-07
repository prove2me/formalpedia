-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:09:36.943638+00:00
-- url     : https://prove2.me/submissions/84248864-2022-4db2-b04f-57645b9e759b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_mem_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_exponent_sum_eq_of_mem_doubleCoset

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ) := by
  apply projectiveDominant_exponent_sum_eq_of_mem_doubleCoset k a b
  apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
    k a.toDominant b.toDominant
  exact hinter
end QEC.Coding.HighDimensionalExpander.SphericalHecke
