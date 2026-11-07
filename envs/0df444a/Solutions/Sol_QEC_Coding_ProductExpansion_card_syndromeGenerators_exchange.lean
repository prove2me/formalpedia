-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_syndromeGenerators_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:17.232202+00:00
-- url     : https://prove2.me/submissions/ef6f8d9a-e836-4fb0-985c-59428ba32a5a

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (y : Word F W)
    (hy : h'.mulVec y ∈ syndromeSpan h' C)
    (hCoordinate : (b.repr ⟨h'.mulVec y, hy⟩) c ≠ 0) :
    (insert y (C.erase c.1)).card = C.card := by
  classical
  have hyNotErase : y ∉ C.erase c.1 := by
    intro hyErase
    let a : C := ⟨y, Finset.mem_of_mem_erase hyErase⟩
    have haNe : a ≠ c := by
      intro heq
      exact (Finset.ne_of_mem_erase hyErase) (congrArg Subtype.val heq)
    have hSame : (⟨h'.mulVec y, hy⟩ : syndromeSpan h' C) = b a := by
      apply Subtype.ext
      exact (hb a).symm
    apply hCoordinate
    rw [hSame, b.repr_self]
    simp [haNe]
  rw [Finset.card_insert_of_notMem hyNotErase]
  have hc : c.1 ∈ C := c.2
  have hErase := Finset.card_erase_add_one hc
  omega
end QEC.Coding.ProductExpansion
