-- Prove2me | solution 1 for ThreeSum.Parameters.all_costs_le_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:22.16414+00:00
-- url     : https://prove2.me/submissions/4a5b5433-2625-4f36-9af1-fbe854f68d77

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_E_bounds
import Theorems.Thm_ThreeSum_Parameters_kappa_bound
import Theorems.Thm_ThreeSum_Parameters_initial_entropy_bound
import Theorems.Thm_ThreeSum_Parameters_cost_ledger_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution :
    ∀ t ∈ costLedger E kappa (entropy initialTheta), t ≤ certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    cost_ledger_bounds E_bounds.1 E_bounds.2 kappa_bound initial_entropy_bound
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [certificateExponent] at * <;> linarith
end ThreeSum.Parameters
