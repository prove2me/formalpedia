-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.step_take_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:34.870973+00:00
-- url     : https://prove2.me/submissions/3259c7c1-eaab-4af2-b8df-c7c98ee34742

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
theorem _root_.solution (p : ℤ) (base prev : List ℤ) {i : ℕ} (hi : i < base.length) :
    step p (base.take (i+1)) prev = step p (base.take i) prev ++
      prev.map (fun y => base[i]+p*y) := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [step,List.flatMap_append,List.flatMap_singleton]
end ThreeSum.RadixKeyLists
