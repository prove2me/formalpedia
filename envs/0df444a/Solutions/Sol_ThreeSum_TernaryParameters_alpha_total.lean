-- Prove2me | solution 1 for ThreeSum.TernaryParameters.alpha_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:25.106653+00:00
-- url     : https://prove2.me/submissions/cd5e5233-7463-4ccd-9e95-5c06f0cb941c

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
theorem _root_.solution : alpha0 + alpha1 + alpha2 = 1 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.TernaryParameters
