-- Prove2me | solution 1 for ThreeSum.TernaryParameters.deficit_room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:26.297473+00:00
-- url     : https://prove2.me/submissions/7c8f00c6-ed0b-4f34-a6ca-1514a44e129e

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution : mean / 2 - deficit = (1190021 / 12500000 : ℝ) := by
  norm_num [mean, pi1, pi2, deficit]
end ThreeSum.TernaryParameters
