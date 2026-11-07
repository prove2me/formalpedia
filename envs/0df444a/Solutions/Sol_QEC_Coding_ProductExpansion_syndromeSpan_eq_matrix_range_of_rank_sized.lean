-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.syndromeSpan_eq_matrix_range_of_rank_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:09.266654+00:00
-- url     : https://prove2.me/submissions/b3de5cf6-f735-477b-8a0c-4ce6c067557b

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
omit [Fintype F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    syndromeSpan h' C = LinearMap.range (h' * x).mulVecLin := by
  classical
  let M : Matrix R' W F := h' * x
  have hRangeLe : LinearMap.range M.mulVecLin ≤ syndromeSpan h' C := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    have hColumn : M.col j = h'.mulVec (column x j) := by
      ext i
      simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct, column]
    rw [hColumn]
    exact hSpanning j
  let G : Finset (R' → F) := C.image (fun y => h'.mulVec y)
  have hSpanG : syndromeSpan h' C = Submodule.span F (G : Set (R' → F)) := by
    simp [syndromeSpan, G]
  have hDimG : Module.finrank F (Submodule.span F (G : Set (R' → F))) ≤
      G.card := by
    exact finrank_span_finset_le_card (R := F) G
  have hGCard : G.card ≤ C.card := Finset.card_image_le
  have hDimS : Module.finrank F (syndromeSpan h' C) ≤
      Module.finrank F (LinearMap.range M.mulVecLin) := by
    rw [hSpanG]
    have hRank : Module.finrank F (LinearMap.range M.mulVecLin) = M.rank := rfl
    rw [hRank]
    change Module.finrank F (Submodule.span F (G : Set (R' → F))) ≤ M.rank
    exact hDimG.trans (hGCard.trans (le_of_eq (by simpa [M] using hCard)))
  have hEq := Submodule.eq_of_le_of_finrank_le hRangeLe hDimS
  simpa [M] using hEq.symm
end QEC.Coding.ProductExpansion
