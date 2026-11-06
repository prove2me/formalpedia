-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signal_difference
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:54.666418+00:00
-- url     : https://prove2.me/submissions/8d72a99e-cfc6-48b7-a8ed-c00daad7c222

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_Geometry_signal_difference

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution (s t : ℝ) : signal s - signal t = s - t := by
  unfold signal signalAt
  ring
