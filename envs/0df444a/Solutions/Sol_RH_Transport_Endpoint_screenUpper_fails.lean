-- Prove2me | solution 1 for RH.Transport.Endpoint.screenUpper_fails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:34.529071+00:00
-- url     : https://prove2.me/submissions/fbb0ba79-1e0f-4b89-ab1a-a838cd7d438d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution :
    0 < generalEndpointExponent screenUpper witnessDelta (1 / 2) := by
  norm_num [generalEndpointExponent, screenUpper, witnessDelta,
    adaptiveCount, countDenominator]
end RH.Transport.Endpoint
