-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:08:42.629301+00:00
-- url     : https://prove2.me/submissions/d0fa8164-536d-4aca-9b3a-e216141bea25

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
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) (i : Source) :
    linearMapOfBasisImages (F := F) image (Pi.single i 1) = image i := by
  classical
  unfold linearMapOfBasisImages
  change (∑ j : Source, (Pi.single i (1 : F) : Word F Source) j • image j) =
    image i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp
end QEC.Coding.ClassicalWeightReduction
