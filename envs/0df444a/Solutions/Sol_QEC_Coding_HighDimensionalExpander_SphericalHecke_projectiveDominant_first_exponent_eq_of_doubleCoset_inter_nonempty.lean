-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:45.300915+00:00
-- url     : https://prove2.me/submissions/0274e247-82cb-48a1-8d81-2e775785b065

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_first_exponent_le_of_mem_doubleCoset

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
    a.toDominant.exponent (0 : Fin (n + 1)) =
      b.toDominant.exponent (0 : Fin (n + 1)) := by
  have hab : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k a.toDominant b.toDominant
    exact hinter
  have hba : dominantCoweight k b.toDominant ∈
      projectiveDominantDoubleCoset k a := by
    apply dominantCoweight_mem_of_doubleCoset_inter_nonempty
      k b.toDominant a.toDominant
    exact ⟨hinter.choose, hinter.choose_spec.2, hinter.choose_spec.1⟩
  exact le_antisymm
    (projectiveDominant_first_exponent_le_of_mem_doubleCoset k a b hab)
    (projectiveDominant_first_exponent_le_of_mem_doubleCoset k b a hba)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
