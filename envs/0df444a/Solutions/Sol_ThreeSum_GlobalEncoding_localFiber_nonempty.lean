-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.localFiber_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:06.609137+00:00
-- url     : https://prove2.me/submissions/0452613a-1ea6-4f3b-b5f7-0e66004dd460

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_mapAt_exists
import Theorems.Thm_ThreeSum_GlobalEncoding_mem_localFiber
import Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_represents


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (hh : 0 < h) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).Nonempty := by
  obtain ⟨w, hw, e, ha, hb, hL, hR⟩ :=
    localSchedule_represents hh (a : LocalField h) (b : LocalField h)
  obtain ⟨i, hmap⟩ := mapAt_exists hw
  have hs : Survives h i e := by
    unfold Survives
    rw [hmap, ha, hb]
    exact ⟨hL, hR⟩
  refine ⟨⟨(i, e), hs⟩, (mem_localFiber a b _).mpr ?_⟩
  change HashFamily.hashValue (mapAt h i) (left e) = (a : LocalField h) ∧
    HashFamily.hashValue (mapAt h i) (right e) = (b : LocalField h)
  rw [hmap]
  exact ⟨ha, hb⟩
end ThreeSum.GlobalEncoding
