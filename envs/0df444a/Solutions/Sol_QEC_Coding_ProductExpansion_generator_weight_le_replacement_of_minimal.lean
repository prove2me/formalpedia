-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.generator_weight_le_replacement_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:19.161614+00:00
-- url     : https://prove2.me/submissions/c8faa686-eeab-4e8c-ac8e-027b1bce0ce5

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
import Theorems.Thm_QEC_Coding_ProductExpansion_syndromeSpan_le_of_exchange
import Theorems.Thm_QEC_Coding_ProductExpansion_card_syndromeGenerators_exchange
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
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (j : W)
    (hCoordinate : (b.repr ⟨h'.mulVec (column x j), hSpanning j⟩) c ≠ 0) :
    restrictedHammingWeight A c.1 ≤ restrictedHammingWeight A (column x j) := by
  classical
  let y := column x j
  let D := insert y (C.erase c.1)
  have hCardExchange : D.card = C.card :=
    card_syndromeGenerators_exchange h' C b hb c y (hSpanning j) hCoordinate
  have hCardD : D.card = (h' * x).rank := by
    exact hCardExchange.trans hCard
  have hSpanLe : syndromeSpan h' C ≤ syndromeSpan h' D :=
    syndromeSpan_le_of_exchange h' C b hb c y (hSpanning j) hCoordinate
  have hSpanningD (k : W) : h'.mulVec (column x k) ∈ syndromeSpan h' D :=
    hSpanLe (hSpanning k)
  have hWeightMin := hMin D hCardD hSpanningD
  have hyNotErase : y ∉ C.erase c.1 := by
    intro hyErase
    have hInsert := Finset.card_insert_of_mem hyErase
    have hErase := Finset.card_erase_add_one c.2
    change (insert y (C.erase c.1)).card = (C.erase c.1).card at hInsert
    change (insert y (C.erase c.1)).card = C.card at hCardExchange
    omega
  have hWeightD : generatorRestrictedWeight A D =
      restrictedHammingWeight A y + generatorRestrictedWeight A (C.erase c.1) := by
    simp [D, generatorRestrictedWeight, Finset.sum_insert hyNotErase]
  have hWeightC : generatorRestrictedWeight A (C.erase c.1) +
      restrictedHammingWeight A c.1 = generatorRestrictedWeight A C := by
    simpa [generatorRestrictedWeight] using
      Finset.sum_erase_add C (restrictedHammingWeight A) c.2
  change restrictedHammingWeight A c.1 ≤ restrictedHammingWeight A y
  omega
end QEC.Coding.ProductExpansion
