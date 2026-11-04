-- Prove2me | solution 1 for ThreeSum.WantedPairs.pairs_nodup_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:16.858202+00:00
-- url     : https://prove2.me/submissions/f699357a-b97f-4a36-b8d1-95fb66626a38

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_SourceBucketView_nodup_indices


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution {μ : ℕ → ℤ} {offsets flat NR NL M : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) : (pairs μ offsets flat left NL).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    exact (SourceBucketView.nodup_indices H hr (hl i (List.mem_range.mp hi))).map
      (fun _ _ he => congrArg Prod.snd he)
  · apply (List.nodup_range (n := NL)).imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hp
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hq
    exact hij ((congrArg Prod.fst ha).trans (congrArg Prod.fst hb).symm)
end ThreeSum.WantedPairs
