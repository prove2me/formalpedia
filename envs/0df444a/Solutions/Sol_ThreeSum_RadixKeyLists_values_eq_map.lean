-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.values_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:43.983941+00:00
-- url     : https://prove2.me/submissions/3dae013d-836a-4307-9a66-313130c379a9

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
theorem _root_.solution (p : ℤ) (raw : α → ℤ) (base : List α) (j : ℕ) :
    values p (base.map raw) j = (tuples base j).map (Radix.positionalHash p raw) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [values,step,tuples,List.flatMap_map,List.map_flatMap,List.map_map,ih]
    apply List.flatMap_congr
    intro a ha
    simp only [Function.comp_def,Radix.positionalHash]
end ThreeSum.RadixKeyLists
