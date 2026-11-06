-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:11.912463+00:00
-- url     : https://prove2.me/submissions/0d862866-b7c3-4f86-b2ce-7e1301a390fa

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F] [Fintype Check]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution {n : Nat}
    (i : Fin n) (j : Fin (n - 1)) :
    (optionalSingle (F := F) (pathPrevious i) +
        optionalSingle (F := F) (pathNext i)) j =
      (Pi.single (pathLeft j) 1 + Pi.single (pathRight j) 1 : Word F (Fin n)) i := by
  classical
  simp only [Pi.add_apply, optionalSingle_pathPrevious_apply,
    optionalSingle_pathNext_apply, Pi.single_apply]
  by_cases hLeft : pathLeft j = i
  · have hLeft' : i = pathLeft j := hLeft.symm
    by_cases hRight : pathRight j = i
    · have hRight' : i = pathRight j := hRight.symm
      rw [if_pos hRight, if_pos hLeft, if_pos hLeft', if_pos hRight']
    · have hRight' : i ≠ pathRight j := fun h => hRight h.symm
      rw [if_neg hRight, if_pos hLeft, if_pos hLeft', if_neg hRight']
      simp only [zero_add, add_zero]
  · have hLeft' : i ≠ pathLeft j := fun h => hLeft h.symm
    by_cases hRight : pathRight j = i
    · have hRight' : i = pathRight j := hRight.symm
      rw [if_pos hRight, if_neg hLeft, if_neg hLeft', if_pos hRight']
      simp only [zero_add, add_zero]
    · have hRight' : i ≠ pathRight j := fun h => hRight h.symm
      rw [if_neg hRight, if_neg hLeft, if_neg hLeft', if_neg hRight']
end QEC.Coding.ClassicalWeightReduction
