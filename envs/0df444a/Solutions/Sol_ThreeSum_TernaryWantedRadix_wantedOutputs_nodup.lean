-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.wantedOutputs_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:14.095098+00:00
-- url     : https://prove2.me/submissions/6f36c547-5d1e-4d19-80ce-53204d4523da

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_localBucket_nodup
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) : ∀ j x, (wantedOutputs p raws j x).Nodup := by
  intro j
  induction j with
  | zero => intro x; simp [wantedOutputs]
  | succ j ih =>
    intro x
    apply List.nodup_flatMap.mpr
    constructor
    · intro i hi
      exact (ih _).map (fun _ _ h => (List.cons.inj h).2)
    · exact (localBucket_nodup p raws x).imp (fun {a b} hab ys ha hb => by
        obtain ⟨tail,_,rfl⟩ := List.mem_map.mp ha
        obtain ⟨other,_,h⟩ := List.mem_map.mp hb
        exact hab (List.cons.inj h).1.symm)
end ThreeSum.TernaryWantedRadix
