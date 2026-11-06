-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.boundary_exact
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:10.313611+00:00
-- url     : https://prove2.me/submissions/c3bf38ec-b71a-4c96-8f4f-4d84b2f3faea

import Definitions.Def_Transport_TunedEndpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section

theorem solution : boundary = (4374785349 / 5000000000 : ℝ) := by
  norm_num [boundary, perturbation]
