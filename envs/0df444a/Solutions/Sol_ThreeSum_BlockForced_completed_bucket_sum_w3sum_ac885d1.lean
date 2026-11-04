-- Prove2me | solution 1 for ThreeSum.BlockForced.completed_bucket_sum_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:10.818368+00:00
-- url     : https://prove2.me/submissions/ea5a280f-4e6b-41df-9d43-b0c3a2cd7881

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Theorems.Thm_ThreeSum_BlockForced_forced_left_completion
import Theorems.Thm_ThreeSum_BlockForced_forced_right_completion
import Theorems.Thm_ThreeSum_BlockForced_residual_mem
import Theorems.Thm_ThreeSum_BlockForced_residual_injective
import Theorems.Thm_ThreeSum_BlockForced_residual_surjective
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_leftWeights_choice
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightWeights_choice
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
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
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i) :
    (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t) =
      ∑ x ∈ (remaining I (outputRows q)).powerset,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
  calc
    _ = ∑ x ∈ admissibleResiduals q I u,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
      apply Finset.sum_bij (fun t _ => residual I t)
      · exact residual_mem q I u hu
      · intro s hs t ht he
        exact residual_injective q I u hs ht he
      · intro x hx
        obtain ⟨t, ht, he⟩ := residual_surjective q I u hu x hx
        exact ⟨t, ht, he⟩
      · intro t ht
        have hq := (Finset.mem_filter.mp ht).2.1
        rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht,
          leftWeights_choice P B b t q hq, rightWeights_choice P d C c t q hq]
    _ = _ := by
      rw [admissibleResiduals, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hL : LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x)
      · by_cases hR : RightAllowed (outputOccurrences q)
            (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))
        · simp only [hL, hR, and_self, ite_true]
        · simp only [hL, hR, and_false, ite_false, rightWeights, mul_zero]
      · simp only [hL, false_and, ite_false, leftWeights, zero_mul]
end ThreeSum.BlockForced
