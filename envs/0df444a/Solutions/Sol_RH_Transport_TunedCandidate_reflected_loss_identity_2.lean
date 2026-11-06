-- Prove2me | solution 2 for RH.Transport.TunedCandidate.reflected_loss_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:31.297203+00:00
-- url     : https://prove2.me/submissions/8dcf0869-1a3b-469a-9804-e94086115bfe

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e d : ℝ) :
    1 + 3 * (e - d) - 2 * (widthAt e - 2 * d) = 5 * e - 1 + d := by
  dsimp [widthAt]
  ring
end RH.Transport.TunedCandidate
