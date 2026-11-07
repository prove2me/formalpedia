-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_supported_syndrome_lift_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:51.369269+00:00
-- url     : https://prove2.me/submissions/fa7125a1-523d-448c-b88c-0da738217060

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_mem_supportedWords_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_generator_span_le_supportedWords
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (C : Finset (Word F W)) (z : R' → F)
    (hz : z ∈ syndromeSpan h' C) :
    ∃ y : Word F W,
      (∀ i ∉ generatorSupport C, y i = 0) ∧ h'.mulVec y = z := by
  classical
  have hMapSpan :
      (Submodule.span F (C : Set (Word F W))).map (Matrix.toLin' h') =
        syndromeSpan h' C := by
    unfold syndromeSpan
    have hFun : (fun y : Word F W => (Matrix.toLin' h') y) =
        (fun y : Word F W => h'.mulVec y) := by
      funext y
      exact Matrix.toLin'_apply h' y
    simpa only [hFun] using
      (Submodule.map_span (Matrix.toLin' h') (C : Set (Word F W)))
  rw [← hMapSpan] at hz
  obtain ⟨y, hySpan, hySyndrome⟩ := hz
  refine ⟨y, ?_, ?_⟩
  · exact (mem_supportedWords_iff (generatorSupport C) y).mp
      ((generator_span_le_supportedWords C) hySpan)
  · simpa only [Matrix.toLin'_apply] using hySyndrome
end QEC.Coding.ProductExpansion
