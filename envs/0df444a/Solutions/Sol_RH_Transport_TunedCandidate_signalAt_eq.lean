-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signalAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:47.162573+00:00
-- url     : https://prove2.me/submissions/8ed71cdf-5f1e-4718-89af-f96c40e5e861

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b s : ℝ) : signalAt e b s = s - 2 / 3 - b / 6 := by
  dsimp [signalAt, lxAt, hAt]
  ring
end RH.Transport.TunedCandidate
