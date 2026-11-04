-- Prove2me | solution 1 for ThreeSum.RawReporting.raw_word_reported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:09.389203+00:00
-- url     : https://prove2.me/submissions/0d14f7f8-f964-4599-a6bd-fd4daa29f76b

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_mem_frontier_iff
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_c2dccdb99e31a4aa
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawReporting
theorem _root_.solution {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (r : RawItem h J α β γ) (hr : r ∈ I) :
    word r ∈ frontier I (wantedOf r) J := by
  apply (mem_frontier_iff I (wantedOf r) le_rfl (word r)).mpr
  refine ⟨r, hr, rfl, ?_⟩
  simpa only [word, partitionWord_length] using (List.take_length (l := word r))
end ThreeSum.RawReporting
