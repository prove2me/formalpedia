-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.degreeFlag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:12.762098+00:00
-- url     : https://prove2.me/submissions/0e2ee39f-49d5-4062-a1e8-2f629566ab81

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) : degreeFlag C q f j≤1 := by
  unfold degreeFlag; split <;> omega
end ThreeSum.LightIrreducibleFinder
