-- Prove2me | solution 1 for ThreeSum.BandEnumeration.owners_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:10.434508+00:00
-- url     : https://prove2.me/submissions/26637260-b351-4bab-ae64-a8b0a9d5f7ce

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) : (owners A B C).Nodup := by
  have hinner : (((List.finRange B.size).map (fun j => (Sum.inl j : B.Index ⊕ C.Index))) ++
      (List.finRange C.size).map Sum.inr).Nodup := by
    apply ((List.nodup_finRange _).map Sum.inl_injective).append
      ((List.nodup_finRange _).map Sum.inr_injective)
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, heq⟩ := List.mem_map.mp hy
    cases heq
  unfold owners
  apply (((List.nodup_finRange _).product (List.nodup_finRange _)).map
    Sum.inl_injective).append
    (((List.nodup_finRange _).product hinner).map Sum.inr_injective)
  apply List.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, heq⟩ := List.mem_map.mp hy
  cases heq
end ThreeSum.BandEnumeration
