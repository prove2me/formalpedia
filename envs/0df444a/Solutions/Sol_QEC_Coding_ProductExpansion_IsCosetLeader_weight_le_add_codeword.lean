-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.IsCosetLeader.weight_le_add_codeword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:46.366319+00:00
-- url     : https://prove2.me/submissions/e6ecaa0d-d3a3-4855-8866-8e5d942fed3d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
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
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
namespace IsCosetLeader
theorem _root_.solution
    {h : Matrix R W F} {y : R → F} {x : Word F W}
    (hx : IsCosetLeader h y x)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier) :
    HammingWeight x ≤ HammingWeight (x + c) := by
  apply hx.2
  rw [Matrix.mulVec_add, hx.1]
  change (Matrix.toLin' h) c = 0 at hc
  rw [Matrix.toLin'_apply] at hc
  simp [hc]
end IsCosetLeader
end QEC.Coding.ProductExpansion
