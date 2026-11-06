-- Prove2me | solution 1 for RH.Transport.Endpoint.boundary_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:27.705364+00:00
-- url     : https://prove2.me/submissions/dc6b1c3a-f1d4-4b68-a080-ec8fb452aea3

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
theorem _root_.solution : boundary = (1399931521 / 1600000000 : ℝ) := by
  norm_num [boundary, perturbation]
end RH.Transport.Endpoint
