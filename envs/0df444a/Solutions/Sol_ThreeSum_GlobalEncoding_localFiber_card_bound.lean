-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.localFiber_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:16.754391+00:00
-- url     : https://prove2.me/submissions/8d7e5ac2-6ff3-4c65-a510-691a1f67a80f

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_retained_survives
import Theorems.Thm_ThreeSum_GlobalEncoding_mem_localFiber
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalHashMoments_local_representation_cap
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


namespace ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
set_option maxHeartbeats 1000000 in
private theorem occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : Occurrence h) :
    ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
      (fun c => occurrence c = i)).card ≤ localBucketCap h ^ 2 := by
  let hits : Finset (Edge (512 * h) h) := Finset.univ.filter fun e =>
    mapAt h i ∈ HashFamily.trimmedPairEvent (left e) (right e)
      (a : LocalField h) (b : LocalField h)
      (leftVertices (512 * h) h) (rightVertices (512 * h) h) (localBucketCap h)
  have hcount : ((Radix.localFiber (localPrime h) rawLeft rawRight a b :
      Finset (RetainedChoice h)).filter (fun c => occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := retained_survives c
      simp only [Survives, hi, ha, hb] at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hs⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hi] using And.intro ha hb⟩
    · intro c hc d hd he
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
      · exact he
  exact hcount.trans (local_representation_cap h (mapAt h i) (a, b))
end ThreeSum.GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution (h : ℕ) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).card ≤
      scheduleSize h * localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : Occurrence h,
        ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
          (fun c => occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Occurrence h, localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact occurrence_fiber_bound h a b i
    _ = _ := by simp [Occurrence]
end ThreeSum.GlobalEncoding
