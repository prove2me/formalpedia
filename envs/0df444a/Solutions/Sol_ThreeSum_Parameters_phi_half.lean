-- Prove2me | solution 1 for ThreeSum.Parameters.phi_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:34.989226+00:00
-- url     : https://prove2.me/submissions/db403463-2ab5-4e89-9985-2a659157de27

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : phi (1 / 2) = (841 / 200 : ℝ) := by norm_num [phi]
end ThreeSum.Parameters
