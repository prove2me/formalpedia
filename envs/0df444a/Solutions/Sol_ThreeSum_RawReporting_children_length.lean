-- Prove2me | solution 1 for ThreeSum.RawReporting.children_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:59.893019+00:00
-- url     : https://prove2.me/submissions/568aa998-d7a4-40f8-98b1-99f463a46a2b

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_childList_length
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
namespace ThreeSum.RawReporting
theorem _root_.solution {h J k : ℕ} (q : GlobalOutput h J) (hk : k < J) :
    (children q k).length = groupSize h := by
  rw [children, dif_pos hk, childList_length]
  have hc := LayerCounts.mem_vertices.mp (q ⟨k, hk⟩).2.property
  simp only [hc, groupSize]
end ThreeSum.RawReporting
