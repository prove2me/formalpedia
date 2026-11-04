-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.tuples_nodup_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:35.941837+00:00
-- url     : https://prove2.me/submissions/75d9fa56-c3db-4060-8a63-700ac01b1498

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
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
theorem _root_.solution (base : List α) (hbase : base.Nodup) (j : ℕ) :
    (tuples base j).Nodup := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a ha
      exact ih.map (fun xs ys he => (List.cons.inj he).2)
    · exact hbase.imp (fun {a b} hab xs hxs hys => by
        obtain ⟨tail,_,rfl⟩ := List.mem_map.mp hxs
        obtain ⟨other,_,he⟩ := List.mem_map.mp hys
        exact hab (List.cons.inj he).1.symm)
end ThreeSum.RadixKeyLists
