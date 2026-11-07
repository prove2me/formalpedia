-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_inter_ge_distance_sub_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:53.998124+00:00
-- url     : https://prove2.me/submissions/fa93b9f9-5b8b-42df-87c8-025d9b61e61f

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
    [DecidableEq W] (E B : Finset W) (d m : Nat)
    (hE : d ≤ E.card) (hB : Fintype.card W - m ≤ B.card) :
    d - m ≤ (E ∩ B).card := by
  have hMissingSubset : E \ B ⊆ Finset.univ \ B := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
  have hMissingCard := Finset.card_le_card hMissingSubset
  have hUnivMissing : (Finset.univ \ B).card = Fintype.card W - B.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ B)
  rw [hUnivMissing] at hMissingCard
  have hBMax : B.card ≤ Fintype.card W := Finset.card_le_univ B
  have hPartition := Finset.card_inter_add_card_sdiff E B
  omega
end QEC.Coding.ProductExpansion
