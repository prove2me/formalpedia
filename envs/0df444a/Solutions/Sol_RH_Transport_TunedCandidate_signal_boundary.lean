-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:43.323672+00:00
-- url     : https://prove2.me/submissions/556306ec-8394-41f2-958a-20bde8e4be6c

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : signal B = lowExponent := by
  unfold signal signalAt lowExponent lowExponentAt B boundaryAt hAt
  ring
