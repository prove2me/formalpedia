-- Prove2me | solution 1 for RH.Transport.Endpoint.beyond_screenUpper_fails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:03.259928+00:00
-- url     : https://prove2.me/submissions/241f6cc5-0238-48a3-b61f-4008ca0ba3c1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint
import Theorems.Thm_RH_Transport_Endpoint_generalEndpoint_variation
import Theorems.Thm_RH_Transport_Endpoint_witness_slope_pos
import Theorems.Thm_RH_Transport_Endpoint_screenUpper_fails

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution {p : ℝ} (hp : screenUpper ≤ p) :
    0 < generalEndpointExponent p witnessDelta (1 / 2) := by
  have hv := generalEndpoint_variation p screenUpper witnessDelta (1 / 2)
  have hm := mul_nonneg (sub_nonneg.mpr hp) witness_slope_pos.le
  have hb := screenUpper_fails
  linarith only [hv, hm, hb]
end RH.Transport.Endpoint
