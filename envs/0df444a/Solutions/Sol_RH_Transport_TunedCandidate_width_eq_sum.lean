-- Prove2me | solution 1 for RH.Transport.TunedCandidate.width_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:16.581206+00:00
-- url     : https://prove2.me/submissions/c5139a6b-12c1-4bd7-9876-84afaeaf4779

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_Geometry_width_eq_sum

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : width = lx + ly := by
  unfold width lx ly widthAt lxAt lyAt
  ring
