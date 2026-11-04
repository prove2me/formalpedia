-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.codeCatalog_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:15.347068+00:00
-- url     : https://prove2.me/submissions/f9505ada-17fc-4e9c-a7ae-3e0f138a4732

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution (J : ℕ) : (codeCatalog J).card≤2^J := by
  exact (card_filter_le _ _).trans_eq (card_range _)
end ThreeSum.TernaryCarryCode
