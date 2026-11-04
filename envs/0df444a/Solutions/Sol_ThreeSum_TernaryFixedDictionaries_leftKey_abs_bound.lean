-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.leftKey_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:30.837318+00:00
-- url     : https://prove2.me/submissions/51ca391c-cb4c-47c1-b2bd-e50c8d3a5711

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_nonnegative
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_upper


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryFixedDictionaries
theorem _root_.solution (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |leftKey maps r| ≤ ((2*L+1)*p : ℕ) := by
  unfold leftKey
  rw [abs_neg,abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _
end ThreeSum.TernaryFixedDictionaries
