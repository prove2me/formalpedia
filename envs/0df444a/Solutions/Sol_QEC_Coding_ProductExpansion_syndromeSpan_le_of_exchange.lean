-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.syndromeSpan_le_of_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:52.246562+00:00
-- url     : https://prove2.me/submissions/297ff226-dff0-47ba-88dd-74b273f5d9b5

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
import Theorems.Thm_QEC_Coding_ProductExpansion_syndromeBasis_exchange_spans
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
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (y : Word F W)
    (hy : h'.mulVec y ∈ syndromeSpan h' C)
    (hCoordinate : (b.repr ⟨h'.mulVec y, hy⟩) c ≠ 0) :
    syndromeSpan h' C ≤ syndromeSpan h' (insert y (C.erase c.1)) := by
  classical
  let D := insert y (C.erase c.1)
  let S := syndromeSpan h' C
  let P := (syndromeSpan h' D).comap S.subtype
  let z : S := ⟨h'.mulVec y, hy⟩
  have hExchange : Submodule.span F (insert z (b '' {a : C | a ≠ c})) = ⊤ :=
    syndromeBasis_exchange_spans h' C b c z hCoordinate
  have hGeneratorsNew : insert z (b '' {a : C | a ≠ c}) ⊆ P := by
    rintro v (rfl | ⟨a, ha, rfl⟩)
    · change h'.mulVec y ∈ syndromeSpan h' D
      apply Submodule.subset_span
      exact ⟨y, Finset.mem_insert_self _ _, rfl⟩
    · change (b a).1 ∈ syndromeSpan h' D
      rw [hb a]
      apply Submodule.subset_span
      refine ⟨a.1, Finset.mem_insert_of_mem ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨by
        intro heq
        exact ha (Subtype.ext heq), a.2⟩
  have hAllBasis (a : C) : (b a).1 ∈ syndromeSpan h' D := by
    have ha : b a ∈ Submodule.span F (insert z (b '' {a : C | a ≠ c})) := by
      rw [hExchange]
      trivial
    exact (Submodule.span_le.mpr hGeneratorsNew) ha
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, rfl⟩
  change h'.mulVec a ∈ syndromeSpan h' (insert y (C.erase c.1))
  simpa only [D, hb ⟨a, ha⟩] using hAllBasis ⟨a, ha⟩
end QEC.Coding.ProductExpansion
