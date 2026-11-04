-- Prove2me | solution 1 for ThreeSum.RawReporting.word_children_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:00.440181+00:00
-- url     : https://prove2.me/submissions/e679bfae-407a-4248-80f1-7bb245cb6176

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_mem_childList
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
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
theorem _root_.solution {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word, partitionWord_length]; exact hj) ∈ children w.2.2 j := by
  have hw := (Finset.mem_filter.mp hr).2
  have hq : tupleOutput r.2.1 = w.2.2 := congrArg (fun x => x.2.2) hw
  have hi := congrFun hq ⟨j, hj⟩
  have hQ : output (edge (r.2.1 ⟨j, hj⟩)) = (w.2.2 ⟨j, hj⟩).2.val :=
    congrArg (fun x => x.2.val) hi
  rw [children, dif_pos hj]
  apply mem_childList.mpr
  simp only [word, partitionWord, List.getElem_ofFn]
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, (edge_data _).1⟩
  rw [← hQ]
  exact Finset.subset_union_left
end ThreeSum.RawReporting
