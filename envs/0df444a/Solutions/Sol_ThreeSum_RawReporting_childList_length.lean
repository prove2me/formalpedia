-- Prove2me | solution 1 for ThreeSum.RawReporting.childList_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:59.344981+00:00
-- url     : https://prove2.me/submissions/78edc811-b9ab-4837-b429-35b6d8891c5d

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
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
theorem _root_.solution {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) :
    (childList Q h).length = Q.card.choose h := by
  simp only [childList, List.length_map, Finset.length_sort,
    Finset.card_map, Finset.card_powersetCard]
end ThreeSum.RawReporting
