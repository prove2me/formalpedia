-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.wanted_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:48.394241+00:00
-- url     : https://prove2.me/submissions/dc3b59aa-9635-4981-85f2-aa633c3ac5c1

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists

set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    (wanted M P xs h J d).card=guardedCount M P xs h J d := by
  rw [wanted,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  unfold guardedCount
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
end ThreeSum.RawAKeyLists
