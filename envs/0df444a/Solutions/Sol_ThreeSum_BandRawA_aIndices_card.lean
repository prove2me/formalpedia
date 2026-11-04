-- Prove2me | solution 1 for ThreeSum.BandRawA.aIndices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:54.16548+00:00
-- url     : https://prove2.me/submissions/07ad0315-6eb4-41da-895a-4784ddf95a81

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) (s : ℕ) :
    (aIndices n g rs s).card=(row n g s (rs.getD s default)).length := by
  unfold aIndices
  rw [card_image_of_injective _ (by intro i j he; exact Nat.add_left_cancel he),card_range]
end ThreeSum.BandRawA
