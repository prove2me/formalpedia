-- Prove2me | solution 1 for RH.Transport.TunedCandidate.hAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:08.431863+00:00
-- url     : https://prove2.me/submissions/adc19d59-7659-4b01-8e20-ffb95b9c4308

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b : ℝ) : hAt e b = 1 - lxAt e b + e := by
  dsimp [hAt, lxAt]
  ring
end RH.Transport.TunedCandidate
