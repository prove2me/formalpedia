-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_generator_coordinate_outside_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:10.282994+00:00
-- url     : https://prove2.me/submissions/0f1819ac-b3a9-4e4b-999c-3e0cbbd32398

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (C T : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ c : C, (b c).1 = h'.mulVec c.1)
    (z : syndromeSpan h' C)
    (hz : (z.1 : R' → F) ∉ syndromeSpan h' T) :
    ∃ c : C, c.1 ∉ T ∧ (b.repr z) c ≠ 0 := by
  classical
  let I : Set C := {c | c.1 ∈ T}
  have hSpanLe : Submodule.span F (b '' I) ≤
      (syndromeSpan h' T).comap (syndromeSpan h' C).subtype := by
    apply Submodule.span_le.mpr
    rintro v ⟨c, hcI, rfl⟩
    change (b c).1 ∈ syndromeSpan h' T
    rw [hb c]
    apply Submodule.subset_span
    exact ⟨c.1, hcI, rfl⟩
  have hNotSpan : z ∉ Submodule.span F (b '' I) := by
    intro hzSpan
    exact hz (hSpanLe hzSpan)
  have hNotSubset : ¬((b.repr z).support : Set C) ⊆ I := by
    intro hSubset
    exact hNotSpan ((b.mem_span_image).mpr hSubset)
  obtain ⟨c, hcSupport, hcNotI⟩ := Set.not_subset.mp hNotSubset
  exact ⟨c, hcNotI, by simpa using hcSupport⟩
end QEC.Coding.ProductExpansion
