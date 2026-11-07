-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_exactRectangleSides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:06.485841+00:00
-- url     : https://prove2.me/submissions/35b0d637-7878-4f68-aab0-ec9398b2d47f

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
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
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (W : Type v) [Fintype W] (m : Nat) :
    Nat.card (exactRectangleSides W m) =
      Nat.choose (Fintype.card W) (Fintype.card W - m) := by
  classical
  rw [Nat.card_congr (exactRectangleSidesEquivPowersetCard W m)]
  simp
end QEC.Coding.ProductExpansion
