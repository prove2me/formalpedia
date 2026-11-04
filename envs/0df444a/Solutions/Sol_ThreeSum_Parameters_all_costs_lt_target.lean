-- Prove2me | solution 1 for ThreeSum.Parameters.all_costs_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:10.965699+00:00
-- url     : https://prove2.me/submissions/508466c0-5463-474a-8225-79f70f3dabb9

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target
import Theorems.Thm_ThreeSum_Parameters_all_costs_le_certificate

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution :
    ∀ t ∈ costLedger E kappa (entropy initialTheta), t < targetExponent := by
  intro t ht
  exact lt_of_le_of_lt (all_costs_le_certificate t ht) certificate_lt_target
end ThreeSum.Parameters
