-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:43:22.267049+00:00
-- url     : https://prove2.me/submissions/82c932aa-8d95-4895-a894-16f0a43bf7bc

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
    {R : Type u} [Field R] {d : ℕ}
    {A B : GL (Fin d) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    ∃ c : Units R,
      A = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by
  have hcenter : A * B⁻¹ ∈ Subgroup.center (GL (Fin d) R) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    rw [map_mul, map_inv, h]
    simp
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  refine ⟨c, ?_⟩
  calc
    A = (A * B⁻¹) * B := by simp
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by rw [← hc]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
