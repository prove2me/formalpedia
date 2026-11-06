-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.generalEndpoint_variation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:44.850174+00:00
-- url     : https://prove2.me/submissions/93125d2d-f38b-47c5-bcfb-feade883328e

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution (p b q c δ x : ℝ) :
    generalEndpointExponent p b δ x - generalEndpointExponent q c δ x =
      (p - q) * (-1 / 4 + δ + δ * x + 3 * adaptiveCount δ x / 2) +
      (b - c) * (adaptiveCount δ x / 2 - 1 / 3) := by
  unfold generalEndpointExponent
  ring
end RH.Transport.TunedEndpoint
