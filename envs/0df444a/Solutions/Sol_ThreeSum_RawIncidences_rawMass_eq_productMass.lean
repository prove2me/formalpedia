-- Prove2me | solution 1 for ThreeSum.RawIncidences.rawMass_eq_productMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:42.895816+00:00
-- url     : https://prove2.me/submissions/e3a0b197-b559-465d-902f-5e6f7152ae65

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_witnesses_card_eq_sum
import Theorems.Thm_ThreeSum_RawIncidences_rawMass_eq_sum_witnesses
import Theorems.Thm_ThreeSum_RawIncidences_bucket_product_eq_sum
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


namespace ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
private theorem sum_four_swap {α β γ δ : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℕ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
section OriginalIndices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
end OriginalIndices
end ThreeSum.RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution (h J : ℕ) (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c = productMass h J P d A B C a b c := by
  rw [rawMass_eq_sum_witnesses, Finset.sum_product]
  unfold productMass
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_product, witnesses_card_eq_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hq : globalModulus h J ∣ (a i % P + lift j * P + d) - tupleKey t
  · simp only [hq, and_true, ite_true]
    exact (bucket_product_eq_sum P d B C b c t).symm
  · simp only [hq, and_false, ite_false, Finset.sum_const_zero]
end ThreeSum.RawIncidences
