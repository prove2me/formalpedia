-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.left_mul_mem_dominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:43:01.886844+00:00
-- url     : https://prove2.me/submissions/8698a6cd-0f97-48c4-93c8-16566a72a033

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
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
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ dominantDoubleCoset k weight) :
    h * x ∈ dominantDoubleCoset k weight := by
  rw [dominantDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, z, hz, rfl⟩
  rcases hy with ⟨a, ha, b, hb, rfl⟩
  refine ⟨(h * a) * b, ?_, z, hz, ?_⟩
  · exact ⟨h * a, (maximalCompact k d).mul_mem hh ha,
      b, hb, rfl⟩
  · simp [mul_assoc]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
