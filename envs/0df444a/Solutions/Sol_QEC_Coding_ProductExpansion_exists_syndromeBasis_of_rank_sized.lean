-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_syndromeBasis_of_rank_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:10.778517+00:00
-- url     : https://prove2.me/submissions/3c02fca7-8425-43e0-9ff0-3643b682b72d

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
import Theorems.Thm_QEC_Coding_ProductExpansion_syndromeGenerators_linearIndependent_of_rank_sized
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
    ∃ b : Module.Basis C F (syndromeSpan h' C),
      ∀ c : C, (b c).1 = h'.mulVec c.1 := by
  classical
  let S := syndromeSpan h' C
  have hMem (c : C) : h'.mulVec c.1 ∈ S := by
    apply Submodule.subset_span
    exact ⟨c.1, c.2, rfl⟩
  let v : C → S := fun c => ⟨h'.mulVec c.1, hMem c⟩
  have hLI : LinearIndependent F v := by
    have hAmbient := syndromeGenerators_linearIndependent_of_rank_sized
      h' x C hCard hSpanning
    apply ((S.subtype).linearIndependent_iff (by simp)).mp
    simpa [v, Function.comp_def] using hAmbient
  have hRangeSet : Set.range (fun c : C => h'.mulVec c.1) =
      (fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hSpanVal : Submodule.span F (Set.range
      (fun c : C => h'.mulVec c.1)) = S := by
    rw [hRangeSet]
    rfl
  have hSpanTop : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [(Submodule.span_range_subtype_eq_top_iff S hMem).mpr hSpanVal]
  refine ⟨Module.Basis.mk hLI hSpanTop, ?_⟩
  intro c
  exact congrArg Subtype.val (Module.Basis.mk_apply hLI hSpanTop c)
end QEC.Coding.ProductExpansion
