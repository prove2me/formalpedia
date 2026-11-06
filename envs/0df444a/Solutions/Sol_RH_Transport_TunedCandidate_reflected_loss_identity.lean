-- Prove2me | solution 1 for RH.Transport.TunedCandidate.reflected_loss_identity
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:35.283871+00:00
-- url     : https://prove2.me/submissions/1be5daa7-5efa-4acc-b820-beab24f5d3b1

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution (e d : ℝ) :
    1 + 3 * (e - d) - 2 * (widthAt e - 2 * d) = 5 * e - 1 + d := by
  dsimp [widthAt]
  ring
