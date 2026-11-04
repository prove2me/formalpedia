-- Prove2me | solution 1 for ThreeSum.TernaryParameters.projection_fiber_entropy_lt_half_Hpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:00.945944+00:00
-- url     : https://prove2.me/submissions/57903fa4-70b7-42da-b31f-7e7438cc8014

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_entropy_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by
  linarith [projection_fiber_entropy_bound, Hpi_bounds.1]
end ThreeSum.TernaryParameters
