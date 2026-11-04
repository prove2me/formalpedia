-- Prove2me | solution 1 for ThreeSum.BandRawA.bandPositions_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:28.287186+00:00
-- url     : https://prove2.me/submissions/ddd122d1-0d2d-405a-83b7-7e9adaa523a3

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g a : ℕ) :
    (bandPositions n g a).card=bandLength n g a := by
  unfold bandPositions
  rw [card_image_of_injective _ (by intro i j he; exact Nat.add_left_cancel he),card_range]
end ThreeSum.BandRawA
