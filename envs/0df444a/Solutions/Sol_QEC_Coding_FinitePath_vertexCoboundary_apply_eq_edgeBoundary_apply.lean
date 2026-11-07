-- Prove2me | solution 1 for QEC.Coding.FinitePath.vertexCoboundary_apply_eq_edgeBoundary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:05.633461+00:00
-- url     : https://prove2.me/submissions/f2b9eabb-db2f-4cd1-af8d-2200bed2f631

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.FinitePath
theorem _root_.solution
    {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    vertexCoboundary (F := F) i j = edgeBoundary (F := F) j i := by
  classical
  unfold vertexCoboundary edgeBoundary
  simp only [Pi.add_apply, optionalSingle_previous_apply,
    optionalSingle_next_apply, Pi.single_apply]
  by_cases hLeft : left j = i
  · have hLeft' : i = left j := hLeft.symm
    by_cases hRight : right j = i
    · have hRight' : i = right j := hRight.symm
      rw [if_pos hRight, if_pos hLeft, if_pos hLeft', if_pos hRight']
    · have hRight' : i ≠ right j := fun h => hRight h.symm
      rw [if_neg hRight, if_pos hLeft, if_pos hLeft', if_neg hRight']
      simp only [zero_add, add_zero]
  · have hLeft' : i ≠ left j := fun h => hLeft h.symm
    by_cases hRight : right j = i
    · have hRight' : i = right j := hRight.symm
      rw [if_pos hRight, if_neg hLeft, if_neg hLeft', if_pos hRight']
      simp only [zero_add, add_zero]
    · have hRight' : i ≠ right j := fun h => hRight h.symm
      rw [if_neg hRight, if_neg hLeft, if_neg hLeft', if_neg hRight']
end QEC.Coding.FinitePath
