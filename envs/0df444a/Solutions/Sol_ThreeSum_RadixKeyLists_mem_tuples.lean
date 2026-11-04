-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.mem_tuples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:42.82976+00:00
-- url     : https://prove2.me/submissions/4bf78902-18c8-40a5-8930-97a6f92a5b07

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
theorem _root_.solution (base : List α) (j : ℕ) (xs : List α) :
    xs ∈ tuples base j ↔ xs.length=j ∧ ∀ a ∈ xs, a ∈ base := by
  induction j generalizing xs with
  | zero => cases xs <;> simp [tuples]
  | succ j ih =>
    cases xs with
    | nil => simp [tuples]
    | cons a xs =>
      simp only [tuples,List.mem_flatMap,List.mem_map,List.cons.injEq,
        ih,List.length_cons,Nat.add_right_cancel_iff,List.mem_cons,forall_eq_or_imp]
      constructor
      · rintro ⟨b,hb,ys,⟨hlen,hsub⟩,rfl,rfl⟩
        exact ⟨hlen,hb,hsub⟩
      · rintro ⟨hlen,hb,hsub⟩
        exact ⟨a,hb,xs,⟨hlen,hsub⟩,rfl,rfl⟩
end ThreeSum.RadixKeyLists
