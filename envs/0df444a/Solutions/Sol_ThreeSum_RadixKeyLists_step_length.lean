-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.step_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:58.507372+00:00
-- url     : https://prove2.me/submissions/d6c1a519-b172-422a-b2b4-3e27ddf49cb5

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
theorem _root_.solution (p : ℤ) (base prev : List ℤ) :
    (step p base prev).length=base.length*prev.length :=
  flatMap_length_uniform base _ prev.length (by simp)
end ThreeSum.RadixKeyLists
