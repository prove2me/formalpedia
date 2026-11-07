-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_of_doubleCoset_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:43:54.172053+00:00
-- url     : https://prove2.me/submissions/4819d9bc-1820-4649-aee5-5460fe43459d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] {d : ℕ}
    (a b : DominantCoweight d)
    (hinter : (dominantDoubleCoset k a ∩
      dominantDoubleCoset k b).Nonempty) :
    dominantCoweight k a ∈ dominantDoubleCoset k b := by
  obtain ⟨x, hxa, hxb⟩ := hinter
  rw [dominantDoubleCoset] at hxa
  rcases hxa with ⟨y, hy, right, hright, rfl⟩
  rcases hy with ⟨left, hleft, diagonal, hdiagonal, rfl⟩
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  have hleft' := left_mul_mem_dominantDoubleCoset k b
    ((maximalCompact k d).inv_mem hleft) hxb
  have hright' := right_mul_mem_dominantDoubleCoset k b
    ((maximalCompact k d).inv_mem hright) hleft'
  simpa [mul_assoc] using hright'
end QEC.Coding.HighDimensionalExpander.SphericalHecke
