-- Prove2me | solution 1 for ThreeSum.TernaryParameters.all_costs_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:55.416807+00:00
-- url     : https://prove2.me/submissions/84b6df15-e8e3-4b6b-8452-41f2b5a0c3dc

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_all_costs_lt_certificate
import Theorems.Thm_ThreeSum_TernaryParameters_certificate_lt_target
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution : ∀ t ∈ costLedger, t < targetExponent := by
  intro t ht
  exact lt_trans (all_costs_lt_certificate t ht) certificate_lt_target
end ThreeSum.TernaryParameters
