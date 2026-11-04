-- Prove2me | solution 1 for ThreeSum.BlockForced.residual_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:16.080341+00:00
-- url     : https://prove2.me/submissions/e784c356-cc64-4235-b662-687a7d8ab594

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_WeightedCache3SUM_Alias_06beccee3b095ee8
import Definitions.Def_WeightedCache3SUM_Alias_e2eca5f3bc1b21c8
import Theorems.Thm_ThreeSum_BlockForced_row_forced_prefix
import Theorems.Thm_ThreeSum_BlockForced_suffix_forced_prefix
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_output_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
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
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i)
    (x : Finset (Coord J (512 * h))) (hx : x ∈ admissibleResiduals q I u) :
    ∃ t ∈ completedTuples q I u, residual I t = x := by
  obtain ⟨hx, hL, hR⟩ := Finset.mem_filter.mp hx
  have hxs := Finset.mem_powerset.mp hx
  let S := prefixLeft I u ∪ x
  let V := prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)
  have hd : Disjoint S V := forced_disjoint I (outputRows q) u x hxs
  let t := fromSubsets (outputOccurrences q) S V hL hR hd
  have hq : tupleOutput t = q := output_fromSubsets q S V hL hR hd
    (forced_union I (outputRows q) u hu x hxs)
  have hleft : leftSubset t = S := leftSubset_fromSubsets _ _ _ _ _ _
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, ?_⟩, ?_⟩
  · intro i hi
    have he := congrArg (fun S => row S i) hleft
    simpa only [row_leftSubset, S, row_forced_prefix I (outputRows q) u x hxs hi] using he
  · change join Iᶜ (fun i => (edge (t i)).val.1) = x
    have he : (fun i => (edge (t i)).val.1) = row S := by
      funext i
      simpa only [row_leftSubset] using congrArg (fun S => row S i) hleft
    rw [he]
    exact suffix_forced_prefix I (outputRows q) u x hxs
end ThreeSum.BlockForced
