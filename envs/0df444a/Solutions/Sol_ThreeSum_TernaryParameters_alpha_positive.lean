-- Prove2me | solution 1 for ThreeSum.TernaryParameters.alpha_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:23.818886+00:00
-- url     : https://prove2.me/submissions/cd3969a4-920a-4800-a82a-f20bfcc6a26f

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
theorem _root_.solution : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.TernaryParameters
