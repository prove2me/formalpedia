-- Prove2me | solution 1 for ThreeSum.TernaryParameters.pi_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:14.384584+00:00
-- url     : https://prove2.me/submissions/e8950b49-1f04-44b6-a9cb-9ad1d001d46b

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
theorem _root_.solution : 0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 := by norm_num [pi0, pi1, pi2]
end ThreeSum.TernaryParameters
