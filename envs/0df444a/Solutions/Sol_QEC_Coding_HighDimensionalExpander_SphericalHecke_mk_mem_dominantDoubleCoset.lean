-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_mem_dominantDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:18.937005+00:00
-- url     : https://prove2.me/submissions/3f71f39b-820b-4aa0-85b8-6b3cd73f694b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_eq_localCartanFactors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithLeft_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithRight_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationCoweight_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutation_conj_smithPowerCoweight_eq_dominant
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
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A ∈
      dominantDoubleCoset k (smithDominantCoweight A) := by
  let left : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A)
  let right : PGL(Fin d, LocalFunctionField k) :=
    Matrix.ProjGenLinGroup.mk
      (smithRightGeneralLinearLocal (k := k) (d := d) A)
  let perm : PGL(Fin d, LocalFunctionField k) :=
    permutationCoweight k
      (dominantSortPermutation (smithExponent (k := k) (d := d) A))
  let diagonal : PGL(Fin d, LocalFunctionField k) :=
    smithPowerCoweight (k := k) (d := d) A
  let dominant : PGL(Fin d, LocalFunctionField k) :=
    dominantCoweight k (smithDominantCoweight A)
  have hleft : left ∈ maximalCompact k d :=
    smithLeft_mem_maximalCompact A
  have hright : right ∈ maximalCompact k d :=
    smithRight_mem_maximalCompact A
  have hperm : perm ∈ maximalCompact k d :=
    permutationCoweight_mem_maximalCompact k _
  have hconj : perm * diagonal * perm⁻¹ = dominant :=
    permutation_conj_smithPowerCoweight_eq_dominant A
  have hfactor :
      Matrix.ProjGenLinGroup.mk A =
        (left * perm⁻¹) * dominant * (perm * right⁻¹) := by
    rw [← hconj]
    rw [projective_eq_localCartanFactors A]
    simp [left, right, diagonal, mul_assoc]
  rw [dominantDoubleCoset, Set.mem_mul]
  refine ⟨(left * perm⁻¹) * dominant, ?_, perm * right⁻¹,
    (maximalCompact k d).mul_mem hperm
      ((maximalCompact k d).inv_mem hright), hfactor.symm⟩
  rw [Set.mem_mul]
  exact ⟨left * perm⁻¹,
    (maximalCompact k d).mul_mem hleft
      ((maximalCompact k d).inv_mem hperm),
    dominant, Set.mem_singleton _, rfl⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
