-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.values_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:36.280196+00:00
-- url     : https://prove2.me/submissions/a7abed4f-47ea-442f-b22e-26be571a664c

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Theorems.Thm_ThreeSum_RadixKeyLists_step_length
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
theorem _root_.solution (p : ℤ) (base : List ℤ) (j : ℕ) :
    (values p base j).length=base.length^j := by
  induction j with
  | zero => simp [values]
  | succ j ih => rw [values,step_length,ih,pow_succ']
end ThreeSum.RadixKeyLists
