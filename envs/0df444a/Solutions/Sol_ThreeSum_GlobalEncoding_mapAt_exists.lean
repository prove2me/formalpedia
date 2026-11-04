-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.mapAt_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:18.060255+00:00
-- url     : https://prove2.me/submissions/3bb0ddba-7a01-4431-a587-fbf99ed6412a

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


namespace ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
private theorem exists_list_index {α : Type*} (xs : List α) {n : ℕ}
    (hn : n = xs.length) (x : α) (hx : x ∈ xs) :
    ∃ i : Fin n, xs.get (Fin.cast hn i) = x := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using List.mem_iff_get.mp hx
end ThreeSum.GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} {w : Weight (512 * h) (LocalField h)}
    (hw : w ∈ localSchedule h) : ∃ i : Occurrence h, mapAt h i = w := by
  exact exists_list_index (localSchedule h) (scheduleSize_eq_length h) w hw
end ThreeSum.GlobalEncoding
