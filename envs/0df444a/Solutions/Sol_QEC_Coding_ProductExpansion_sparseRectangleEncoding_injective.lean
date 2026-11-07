-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.sparseRectangleEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:32.746769+00:00
-- url     : https://prove2.me/submissions/7ba4a3bc-8383-4b5c-ac52-45ef701f1bb3

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
    [DecidableEq W]
    (A B : Finset W) (s : Nat) :
    Function.Injective (sparseRectangleEncoding (F := F) A B s) := by
  classical
  intro x y hxy
  have hSupport : rectangleSupport x.1 A B = rectangleSupport y.1 A B := by
    exact congrArg (fun z => z.1.1) hxy
  apply Subtype.ext
  ext i j
  by_cases hij : (i, j) ∈ A ×ˢ B
  · by_cases hxij : x.1 i j = 0
    · have hxNotSupport : (i, j) ∉ rectangleSupport x.1 A B := by
        simp [rectangleSupport, hij, hxij]
      have hyNotSupport : (i, j) ∉ rectangleSupport y.1 A B := by
        simpa [hSupport] using hxNotSupport
      have hyij : y.1 i j = 0 := by
        simpa [rectangleSupport, hij] using hyNotSupport
      exact hxij.trans hyij.symm
    · have hxSupport : (i, j) ∈ rectangleSupport x.1 A B := by
        simp [rectangleSupport, hij, hxij]
      have hySupport : (i, j) ∈ rectangleSupport y.1 A B := by
        simpa [hSupport] using hxSupport
      have hInside := congrArg (fun z =>
        if hp : (i, j) ∈ z.1.1 then some (z.2.2 ⟨(i, j), hp⟩) else none) hxy
      simpa [sparseRectangleEncoding, hxSupport, hySupport] using hInside
  · let p : (Finset.univ \ (A ×ˢ B) : Finset (W × W)) :=
      ⟨(i, j), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hij⟩⟩
    exact congrArg (fun z => z.2.1 p) hxy
end QEC.Coding.ProductExpansion
