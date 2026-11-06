-- Prove2me | solution 1 for RH.Transport.TunedCandidate.extension_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:27.610301+00:00
-- url     : https://prove2.me/submissions/2c625bad-21de-4f95-be50-3a2fcce7a04e

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : zeta < 5 * ell - h := by
  norm_num [zeta, ell, h, hAt, b, p, Geometry.ell]
