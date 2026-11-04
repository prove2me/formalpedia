-- Prove2me | solution 1 for ThreeSum.TernaryParameters.all_costs_lt_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:57.081927+00:00
-- url     : https://prove2.me/submissions/30992958-fb7a-4fe8-8e64-e95874a5eebb

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_ledger_individual_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution : ∀ t ∈ costLedger, t < certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ledger_individual_bounds
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · norm_num [certificateExponent]
end ThreeSum.TernaryParameters
