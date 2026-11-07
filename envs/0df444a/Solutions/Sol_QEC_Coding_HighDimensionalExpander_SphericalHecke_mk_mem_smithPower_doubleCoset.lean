-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_mem_smithPower_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:58:24.653383+00:00
-- url     : https://prove2.me/submissions/eff3d0ea-6b0f-4620-b4c0-a0cc1258a18e

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
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
        ({smithPowerCoweight (k := k) (d := d) A} :
          Set PGL(Fin d, LocalFunctionField k)) *
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
  rw [Set.mem_mul]
  refine ⟨Matrix.ProjGenLinGroup.mk
      (smithLeftGeneralLinearLocal (k := k) (d := d) A) *
        smithPowerCoweight (k := k) (d := d) A, ?_,
      (Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A))⁻¹, ?_, ?_⟩
  · rw [Set.mem_mul]
    exact ⟨_, smithLeft_mem_maximalCompact (k := k) (d := d) A,
      _, Set.mem_singleton _, rfl⟩
  · exact (maximalCompact k d).inv_mem
      (smithRight_mem_maximalCompact (k := k) (d := d) A)
  · exact (projective_eq_localCartanFactors (k := k) (d := d) A).symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
