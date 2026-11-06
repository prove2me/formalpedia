-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.adaptive_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:29.076205+00:00
-- url     : https://prove2.me/submissions/81c4ec0b-568f-4f73-b667-f984cf48a9e1

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint
import Theorems.Thm_RH_Transport_TunedEndpoint_countDenominator_pos
import Theorems.Thm_RH_Transport_TunedEndpoint_certificate_identity
import Theorems.Thm_RH_Transport_TunedEndpoint_certificate_nonnegative
import Theorems.Thm_RH_Transport_Endpoint_certificate_identity
import Theorems.Thm_RH_Transport_Endpoint_certificate_nonnegative
import Theorems.Thm_RH_Transport_Endpoint_countDenominator_pos


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    endpointExponent δ x ≤ -(1 / 1000000000000 : ℝ) := by
  have hJ := countDenominator_pos hdlo hdhi hxlo hxhi
  have hp := certificate_nonnegative hdlo hdhi hxlo hxhi
  rw [certificate_identity δ x (ne_of_gt hJ)] at hp
  have he : 0 ≤ -endpointExponent δ x - saving :=
    (mul_nonneg_iff_of_pos_right hJ).mp hp
  unfold saving at he
  linarith
end RH.Transport.TunedEndpoint
