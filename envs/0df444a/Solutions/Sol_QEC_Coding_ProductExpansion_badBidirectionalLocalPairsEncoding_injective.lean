-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:39.718956+00:00
-- url     : https://prove2.me/submissions/68c06912-ee03-4509-a1f5-fa3012e120e5

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badBidirectionalLocalPairsEncoding_val
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d s m k : Nat) :
    Function.Injective
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k) := by
  intro p q hpq
  apply Subtype.ext
  have hval := congrArg badBidirectionalLocalPairsSumVal hpq
  simpa only [badBidirectionalLocalPairsEncoding_val] using hval
end QEC.Coding.ProductExpansion
