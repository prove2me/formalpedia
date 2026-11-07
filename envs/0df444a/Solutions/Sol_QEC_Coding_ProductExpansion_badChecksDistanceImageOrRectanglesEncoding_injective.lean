-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badChecksDistanceImageOrRectanglesEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:13.768695+00:00
-- url     : https://prove2.me/submissions/7340d7dc-3474-4295-9567-ce81e61130dd

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceImageOrRectanglesEncoding_val
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
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (d s m k : Nat) :
    Function.Injective
      (badChecksDistanceImageOrRectanglesEncoding
        (R := R) h' d s m k) := by
  intro h g heq
  apply Subtype.ext
  have hval := congrArg
    (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)) heq
  simpa only [badChecksDistanceImageOrRectanglesEncoding_val] using hval
end QEC.Coding.ProductExpansion
