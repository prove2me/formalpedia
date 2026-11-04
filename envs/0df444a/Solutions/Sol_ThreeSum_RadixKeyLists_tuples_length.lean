-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.tuples_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:57.40491+00:00
-- url     : https://prove2.me/submissions/4f898320-8a54-4fcf-9804-5307d12e5267

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Theorems.Thm_ThreeSum_RadixKeyLists_flatMap_length_uniform
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}
namespace ThreeSum.RadixKeyLists
theorem _root_.solution (base : List α) (j : ℕ) :
    (tuples base j).length=base.length^j := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    rw [tuples,flatMap_length_uniform base _ (base.length^j) (by simp [ih]),pow_succ']
end ThreeSum.RadixKeyLists
