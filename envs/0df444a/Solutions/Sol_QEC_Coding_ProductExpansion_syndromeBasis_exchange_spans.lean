-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.syndromeBasis_exchange_spans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:12.593197+00:00
-- url     : https://prove2.me/submissions/f0506aec-7b21-403f-b390-b3e175515c3a

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
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (c : C) (z : syndromeSpan h' C)
    (hCoordinate : (b.repr z) c ≠ 0) :
    Submodule.span F (insert z (b '' {a : C | a ≠ c})) = ⊤ := by
  classical
  let I : Set C := {a | a ≠ c}
  have hNotSpan : z ∉ Submodule.span F (b '' I) := by
    intro hz
    have hSubset := (b.mem_span_image).mp hz
    exact hCoordinate (by
      have hcSupport : c ∈ (b.repr z).support := Finsupp.mem_support_iff.mpr hCoordinate
      exact False.elim ((hSubset hcSupport) rfl))
  have hRangeSubset : Set.range b ⊆ insert (b c) (b '' I) := by
    rintro v ⟨a, rfl⟩
    by_cases ha : a = c
    · simp [ha]
    · exact Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩
  have hzOld : z ∈ Submodule.span F (insert (b c) (b '' I)) :=
    Submodule.span_mono hRangeSubset (b.mem_span z)
  have hcNew : b c ∈ Submodule.span F (insert z (b '' I)) :=
    mem_span_insert_exchange hzOld hNotSpan
  apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
  intro a
  by_cases ha : a = c
  · simpa [I, ha] using hcNew
  · apply Submodule.subset_span
    exact Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩
end QEC.Coding.ProductExpansion
