-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.flatMap_length_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:38.528195+00:00
-- url     : https://prove2.me/submissions/ca8620f8-40e0-4f69-bd5d-966320a3d67e

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
theorem _root_.solution (xs : List α) (f : α → List β) (q : ℕ)
    (h : ∀ x ∈ xs, (f x).length=q) : (xs.flatMap f).length=xs.length*q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      h x (by simp),ih (by intro a ha; exact h a (by simp [ha]))]
    ring
end ThreeSum.RadixKeyLists
