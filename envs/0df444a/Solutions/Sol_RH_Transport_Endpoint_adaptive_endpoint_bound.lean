-- Prove2me | solution 1 for RH.Transport.Endpoint.adaptive_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:16.2741+00:00
-- url     : https://prove2.me/submissions/2b03c785-d728-43b8-bac7-620d747075b4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint
import Theorems.Thm_RH_Transport_Endpoint_countDenominator_pos
import Theorems.Thm_RH_Transport_Endpoint_certificate_identity
import Theorems.Thm_RH_Transport_Endpoint_certificate_nonnegative

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    endpointExponent δ x ≤ -(1 / 40000000000 : ℝ) := by
  have hJ := countDenominator_pos hdlo hdhi hxlo hxhi
  have hp := certificate_nonnegative hdlo hdhi hxlo hxhi
  rw [certificate_identity δ x (ne_of_gt hJ)] at hp
  have he : 0 ≤ -endpointExponent δ x - saving :=
    (mul_nonneg_iff_of_pos_right hJ).mp hp
  unfold saving at he
  linarith
end RH.Transport.Endpoint
