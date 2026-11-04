-- Prove2me | solution 1 for ThreeSum.LightColoredTwoSum.flag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:08.396556+00:00
-- url     : https://prove2.me/submissions/f165ae51-56cc-4f56-8e99-b6f380a4bb67

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
namespace ThreeSum.LightColoredTwoSum
theorem _root_.solution (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) :
    flag scan target m j bad sign≤1 := by unfold flag; split <;> omega
end ThreeSum.LightColoredTwoSum
