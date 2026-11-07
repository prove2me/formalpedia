-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.sparseWordEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:35.577234+00:00
-- url     : https://prove2.me/submissions/59266ae8-3e3d-493e-bed9-45eec4af94b6

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
omit [Fintype F]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (d : Nat) :
    Function.Injective (sparseWordEncoding (F := F) (W := W) d) := by
  classical
  intro c e hce
  have hSupport : hammingSupport c.1 = hammingSupport e.1 :=
    congrArg (fun z => z.1.1) hce
  apply Subtype.ext
  funext i
  by_cases hci : c.1 i = 0
  · have hiNotC : i ∉ hammingSupport c.1 := by
      simp [hammingSupport, hci]
    have hiNotE : i ∉ hammingSupport e.1 := by simpa [hSupport] using hiNotC
    have hei : e.1 i = 0 := by simpa [hammingSupport] using hiNotE
    exact hci.trans hei.symm
  · have hiC : i ∈ hammingSupport c.1 := by simp [hammingSupport, hci]
    have hiE : i ∈ hammingSupport e.1 := by simpa [hSupport] using hiC
    have hInside := congrArg (fun z =>
      if hi : i ∈ z.1.1 then some (z.2 ⟨i, hi⟩) else none) hce
    simpa [sparseWordEncoding, hiC, hiE] using hInside
end QEC.Coding.ProductExpansion
