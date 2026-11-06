-- Prove2me | solution 1 for RH.Transport.TunedCandidate.ly_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:49.05162+00:00
-- url     : https://prove2.me/submissions/2122090d-edb2-41cc-8b94-0f8a6a1644cf

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_Geometry_ly_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : ly = lx + b := by
  unfold ly lx lyAt lxAt
  ring
