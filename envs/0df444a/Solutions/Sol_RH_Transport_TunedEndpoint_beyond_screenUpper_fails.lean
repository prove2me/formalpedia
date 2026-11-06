-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.beyond_screenUpper_fails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:02.147967+00:00
-- url     : https://prove2.me/submissions/41058572-96a2-4ce6-96f4-68d277b9b495

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint
import Theorems.Thm_RH_Transport_TunedEndpoint_weights_positive
import Theorems.Thm_RH_Transport_TunedEndpoint_combinedSlope_positive
import Theorems.Thm_RH_Transport_TunedEndpoint_weighted_endpoint_identity

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution {p : ℝ} (hp : screenUpper ≤ p) (b : ℝ) :
    ¬ (generalEndpointExponent p b witnessDelta1 (1 / 2) < 0 ∧
      generalEndpointExponent p b witnessDelta2 (1 / 2) < 0) := by
  intro hneg
  obtain ⟨hw1, hw2⟩ := weights_positive
  have hsum := add_neg (mul_neg_of_pos_of_neg hw1 hneg.1)
    (mul_neg_of_pos_of_neg hw2 hneg.2)
  rw [weighted_endpoint_identity] at hsum
  have hnonneg := mul_nonneg combinedSlope_positive.le (sub_nonneg.mpr hp)
  linarith only [hsum, hnonneg]
end RH.Transport.TunedEndpoint
