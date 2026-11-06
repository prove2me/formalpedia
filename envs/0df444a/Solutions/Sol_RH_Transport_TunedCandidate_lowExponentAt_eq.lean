-- Prove2me | solution 1 for RH.Transport.TunedCandidate.lowExponentAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:18.851894+00:00
-- url     : https://prove2.me/submissions/702b337a-fdc9-48fe-abda-d3b355608048

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b : ℝ) :
    lowExponentAt e b = 1 / 4 - e / 4 - b / 6 := by
  dsimp [lowExponentAt, lxAt]
  ring
end RH.Transport.TunedCandidate
