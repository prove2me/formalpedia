-- Prove2me | solution 1 for RH.Transport.TunedCandidate.lyAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:18.301417+00:00
-- url     : https://prove2.me/submissions/1a76689d-a5e2-49d6-a457-16518855020d

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b : ℝ) : lyAt e b = lxAt e b + b := by
  dsimp [lyAt, lxAt]
  ring
end RH.Transport.TunedCandidate
