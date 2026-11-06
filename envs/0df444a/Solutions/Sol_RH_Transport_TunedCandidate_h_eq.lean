-- Prove2me | solution 1 for RH.Transport.TunedCandidate.h_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:44.76076+00:00
-- url     : https://prove2.me/submissions/b4312ff7-e9a4-4b2a-91b9-6d9a986d312f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_Geometry_h_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : h = 1 - lx + ell := by
  dsimp [h, lx, hAt, lxAt]
  ring
