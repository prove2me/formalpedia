-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_firstTwoSum_eq_of_doubleCoset_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:12:23.419687+00:00
-- url     : https://prove2.me/submissions/9b255ea9-b0d9-4564-86f6-a0a5e6f42869

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) =
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) := by
  have hab : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b := by
    exact dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k a.toDominant b.toDominant hinter
  have hba : dominantCoweight k b.toDominant ∈
      projectiveDominantDoubleCoset k a := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k b.toDominant a.toDominant
    rw [Set.inter_comm]
    exact hinter
  exact le_antisymm
    (projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
      k a b hab)
    (projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
      k b a hba)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
