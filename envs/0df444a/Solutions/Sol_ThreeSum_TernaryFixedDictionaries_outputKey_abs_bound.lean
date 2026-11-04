-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.outputKey_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:52.907178+00:00
-- url     : https://prove2.me/submissions/07201aee-2fdc-49ad-a68a-b935ff31ba5b

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawOutput_abs_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryFixedDictionaries
theorem _root_.solution (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : OutputBlock L π I) : |blockKey maps r| ≤ ((2*L+2)*p : ℕ) :=
  rawOutput_abs_bound _ _
end ThreeSum.TernaryFixedDictionaries
