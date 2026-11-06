-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.boundary_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:10:40.781247+00:00
-- url     : https://prove2.me/submissions/e1157933-8af0-49f1-831e-47cb79e69f8f

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single

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
theorem _root_.solution (i : WeightReducedBit R) :
    boundary (F := F) R (Pi.single i 1) = basisBoundary (F := F) R i := by
  exact linearMapOfBasisImages_single (F := F) _ _
end QEC.Coding.ClassicalWeightReduction
