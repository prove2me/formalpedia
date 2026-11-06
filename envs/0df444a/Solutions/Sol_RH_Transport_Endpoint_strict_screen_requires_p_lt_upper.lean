-- Prove2me | solution 1 for RH.Transport.Endpoint.strict_screen_requires_p_lt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:34.130247+00:00
-- url     : https://prove2.me/submissions/dbd7aa1e-091b-46e2-a9c7-ba390ca2c60a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint
import Theorems.Thm_RH_Transport_Endpoint_witness_in_domain
import Theorems.Thm_RH_Transport_Endpoint_beyond_screenUpper_fails

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution {p : ℝ}
    (hgood : ∀ δ x : ℝ, (1 / 50 : ℝ) ≤ δ → δ ≤ 3 / 4 →
      0 ≤ x → x ≤ 1 / 2 → generalEndpointExponent p δ x < 0) :
    p < screenUpper := by
  by_contra hp
  have hpos := beyond_screenUpper_fails (le_of_not_gt hp)
  obtain ⟨hdlo, hdhi, hxlo, hxhi⟩ := witness_in_domain
  have hneg := hgood witnessDelta (1 / 2) hdlo hdhi hxlo hxhi
  linarith only [hpos, hneg]
end RH.Transport.Endpoint
