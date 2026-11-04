-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.idxOf_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:05.858801+00:00
-- url     : https://prove2.me/submissions/141a81a7-0527-41ae-bdbf-722c266a567b

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (l : List ι) (x : ι) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.idxOf_cons,hf.beq_eq,ih]
end ThreeSum.WeightEnumeration
