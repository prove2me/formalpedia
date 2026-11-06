-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.weights_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:46.507217+00:00
-- url     : https://prove2.me/submissions/60d1285d-0316-408a-9fcd-4e4a3c9fff56

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
theorem _root_.solution : 0 < weight1 ∧ 0 < weight2 := by
  norm_num [weight1, weight2, witnessDelta1, witnessDelta2,
    adaptiveCount, Endpoint.adaptiveCount, Endpoint.countDenominator]
end RH.Transport.TunedEndpoint
