-- Prove2me | solution 1 for ThreeSum.TernarySignedLayout.offset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:20.717697+00:00
-- url     : https://prove2.me/submissions/814913eb-d1f2-417a-a352-0c7d72383cf6

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction
namespace ThreeSum.TernarySignedLayout
theorem _root_.solution {J i : ℕ} (hi : i<J+2) : offset J i<J+2 := by
  unfold offset
  split_ifs <;> omega
end ThreeSum.TernarySignedLayout
