-- Prove2me | solution 1 for ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:12.930086+00:00
-- url     : https://prove2.me/submissions/4885e861-370f-4ea1-9ade-4eb5f9388dd6

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Theorems.Thm_ThreeSum_StoredReporting_take_prefixRows
import Theorems.Thm_ThreeSum_StoredReporting_completions_eq_completedTuples
import Definitions.Def_WeightedCache3SUM_Alias_fa72617747e17f03
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Definitions.Def_WeightedCache3SUM_Alias_bfbfce5ef1eaf3a6
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_5ac87a5d705087bf
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.StoredReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.StoredReporting
theorem _root_.solution {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    storedQueryValue P d A B C a b c w k pre =
      (prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) := by
  unfold storedQueryValue
  split
  next hp =>
    have hpre := take_prefixRows (J := J) pre hp.1 hk
    have he := transformPrefixValue_eq_bucket_sum P d B C b c w.2.2
      (prefixIndices J k) (prefixRows pre) (fun i hi => hp.2 i (mem_prefixIndices.mp hi))
    rw [prefixQuery_eq_bucketPrefixMass, bucketPrefixMass]
    by_cases hkey : w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2
    · simp only [hkey, ite_true]
      rw [← completions_eq_completedTuples, hpre] at he
      exact he
    · simp only [hkey, ite_false, Nat.cast_zero]
  next hp =>
    have hz : prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre = 0 := by
      by_contra hn
      exact hp (positivePrefix_valid _ w pre hk (Nat.pos_of_ne_zero hn))
    simp only [hz, Nat.cast_zero]
end ThreeSum.StoredReporting
