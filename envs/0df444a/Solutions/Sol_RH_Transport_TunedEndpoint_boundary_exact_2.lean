-- Prove2me | solution 2 for RH.Transport.TunedEndpoint.boundary_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:43.509688+00:00
-- url     : https://prove2.me/submissions/0df06d3b-7dd8-405a-aeba-31db9697f6d9

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
theorem _root_.solution : boundary = (4374785349 / 5000000000 : ℝ) := by
  norm_num [boundary, perturbation]
end RH.Transport.TunedEndpoint
