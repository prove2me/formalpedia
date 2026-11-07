-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_mem_dominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:21.369794+00:00
-- url     : https://prove2.me/submissions/51869970-e7f0-4211-ac82-5e45ec11592c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_dominantCoweight
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mem_maximalCompact
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
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d)
    {x : PGL(Fin d, LocalFunctionField k)}
    (hx : x ∈ dominantDoubleCoset k weight) :
    projectiveTranspose x ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, right, hright, rfl⟩
  rcases hy with ⟨left, hleft, diagonal, hdiagonal, rfl⟩
  have hdiag : diagonal = dominantCoweight k weight :=
    Set.mem_singleton_iff.mp hdiagonal
  subst diagonal
  refine ⟨projectiveTranspose right * dominantCoweight k weight, ?_,
    projectiveTranspose left, projectiveTranspose_mem_maximalCompact k hleft,
    ?_⟩
  · exact ⟨projectiveTranspose right,
      projectiveTranspose_mem_maximalCompact k hright,
      dominantCoweight k weight, Set.mem_singleton _, rfl⟩
  · rw [projectiveTranspose_mul, projectiveTranspose_mul,
      projectiveTranspose_dominantCoweight]
    simp [mul_assoc]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
