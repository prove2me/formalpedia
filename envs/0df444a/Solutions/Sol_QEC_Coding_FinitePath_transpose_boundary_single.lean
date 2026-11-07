-- Prove2me | solution 1 for QEC.Coding.FinitePath.transpose_boundary_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:44.204199+00:00
-- url     : https://prove2.me/submissions/c99a48e8-c14f-4843-b065-4c850071ae29

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_FinitePath_vertexCoboundary_apply_eq_edgeBoundary_apply
import Theorems.Thm_QEC_Coding_FinitePath_boundary_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.FinitePath.boundary_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [DecidableEq F]
namespace QEC.Coding.FinitePath
theorem _root_.solution {n : Nat} (j : Fin n) :
    wordLinearMapTranspose (boundary (F := F)) (Pi.single j 1) =
      edgeBoundary (F := F) j := by
  classical
  ext i
  unfold wordLinearMapTranspose boundary
  dsimp
  rw [Fintype.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_mul]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_mul]
      exact vertexCoboundary_apply_eq_edgeBoundary_apply (F := F) i j
    · intro i' _ hne
      simp [hne]
    · simp
  · intro j' hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
end QEC.Coding.FinitePath
