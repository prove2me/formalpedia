-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.syndromeGenerators_linearIndependent_of_rank_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:36.777104+00:00
-- url     : https://prove2.me/submissions/d75e63fd-5ad6-4d4e-9b13-453f597bd4ad

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
import Theorems.Thm_QEC_Coding_ProductExpansion_syndromeSpan_eq_matrix_range_of_rank_sized
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
omit [Fintype F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    LinearIndependent F (fun c : C => h'.mulVec c.1) := by
  classical
  have hRangeSet : Set.range (fun c : C => h'.mulVec c.1) =
      (fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  apply (linearIndependent_iff_card_eq_finrank_span).mpr
  change Fintype.card C = Module.finrank F
    (Submodule.span F (Set.range (fun c : C => h'.mulVec c.1)))
  rw [hRangeSet]
  change Fintype.card C = Module.finrank F (syndromeSpan h' C)
  rw [syndromeSpan_eq_matrix_range_of_rank_sized h' x C hCard hSpanning]
  simpa [Matrix.rank] using hCard
end QEC.Coding.ProductExpansion
