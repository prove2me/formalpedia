-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_lowWeightWords_lt_le_choose_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:57.989613+00:00
-- url     : https://prove2.me/submissions/167d7775-e3c2-41ed-8c41-20237227df41

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_sparseWordEncoding_injective
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
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (d : Nat) :
    Nat.card {c : Word F W // HammingWeight c < d} ≤
      ∑ t : Fin d, Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1 := by
  classical
  have hEncode : Nat.card {c : Word F W // HammingWeight c < d} ≤
      Nat.card (Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
        S.1 → F) :=
    Nat.card_le_card_of_injective (sparseWordEncoding (F := F) (W := W) d)
      (sparseWordEncoding_injective (F := F) (W := W) d)
  calc
    Nat.card {c : Word F W // HammingWeight c < d} ≤
        Nat.card (Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
          S.1 → F) := hEncode
    _ = ∑ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d},
        (Nat.card F) ^ S.1.card := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = ∑ z : Σ t : Fin d,
        (Finset.univ : Finset W).powersetCard t.1,
        (Nat.card F) ^ z.1.1 := by
      apply Fintype.sum_equiv
        (smallSubsetsEquivSigmaPowersetCard (Finset.univ : Finset W) d)
      intro S
      rfl
    _ = ∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.card_powersetCard]
end QEC.Coding.ProductExpansion
