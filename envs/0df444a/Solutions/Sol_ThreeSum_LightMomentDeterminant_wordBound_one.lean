-- Prove2me | solution 1 for ThreeSum.LightMomentDeterminant.wordBound_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:55.575209+00:00
-- url     : https://prove2.me/submissions/f21dabf7-2468-40d6-9cfe-fc2430097262

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
namespace ThreeSum.LightMomentDeterminant
theorem _root_.solution (U : ℤ) (h : ℕ) : 1≤wordBound U h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih => exact ih.trans (le_max_left _ _)
end ThreeSum.LightMomentDeterminant
