-- Prove2me | solution 1 for ThreeSum.WantedPairs.selected_join_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:50.718078+00:00
-- url     : https://prove2.me/submissions/18a37256-4956-4b27-9784-22900bdcc4b3

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_WantedPairs_count_global
import Theorems.Thm_ThreeSum_RawAKeyLists_selected_guarded_bound
import Theorems.Thm_ThreeSum_RawAKeyLists_wantedCount_eq_guardedCount


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    M*count
      (fun i => LightResidues.residue M 1
        ((RawAKeyLists.keys P xs).getD i 0+RawAKeyLists.selected M P xs h J))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length (RawAKeyLists.keys P xs).length ≤
      3*xs.length*(GlobalEncoding.scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by
  rw [count_global M (Nat.pos_of_ne_zero (NeZero.ne M)),RawAKeyLists.wantedCount_eq_guardedCount]
  exact RawAKeyLists.selected_guarded_bound M P xs h J
end ThreeSum.WantedPairs
