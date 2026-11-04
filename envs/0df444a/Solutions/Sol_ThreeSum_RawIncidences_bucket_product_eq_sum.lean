-- Prove2me | solution 1 for ThreeSum.RawIncidences.bucket_product_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:17.822111+00:00
-- url     : https://prove2.me/submissions/9b59a69b-f583-4968-ac74-d5681b9df014

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ∑ j ∈ B, ∑ k ∈ C,
        if globalModulus h J ∣ b j % P - tupleLeft t ∧
          globalModulus h J ∣ c k % P + d - tupleRight t then 1 else 0 := by
  unfold leftBucket rightBucket
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hL : globalModulus h J ∣ b j % P - tupleLeft t <;>
    by_cases hR : globalModulus h J ∣ c k % P + d - tupleRight t <;> simp [hL, hR]
end ThreeSum.RawIncidences
