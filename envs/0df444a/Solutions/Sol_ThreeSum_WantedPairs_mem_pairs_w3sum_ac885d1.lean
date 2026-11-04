-- Prove2me | solution 1 for ThreeSum.WantedPairs.mem_pairs_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:36.958228+00:00
-- url     : https://prove2.me/submissions/b97179fb-573b-42b3-8397-5bc7a08f2eeb

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_SourceBucketView_mem_indices


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution {μ : ℕ → ℤ} {offsets flat NR NL M i j : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) :
    (i,j) ∈ pairs μ offsets flat left NL ↔ i < NL ∧ j < NR ∧ right j=left i := by
  constructor
  · intro hh
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hh
    have ha' : a < NL := List.mem_range.mp ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hai : a=i := congrArg Prod.fst he
    have hbj : b=j := congrArg Prod.snd he
    subst a
    subst b
    exact ⟨ha',(SourceBucketView.mem_indices H hr (hl i ha')).mp hb⟩
  · rintro ⟨hi,hj,hkey⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr hi,?_⟩
    apply List.mem_map.mpr
    exact ⟨j,(SourceBucketView.mem_indices H hr (hl i hi)).mpr ⟨hj,hkey⟩,rfl⟩
end ThreeSum.WantedPairs
