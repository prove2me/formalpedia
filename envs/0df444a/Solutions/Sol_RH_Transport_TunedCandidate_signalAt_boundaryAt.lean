-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signalAt_boundaryAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:04.623759+00:00
-- url     : https://prove2.me/submissions/48f54ef6-594e-4b37-983a-b7a02f707cfd

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_signalAt_eq
import Theorems.Thm_RH_Transport_TunedCandidate_lowExponentAt_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b : ℝ) :
    signalAt e b (boundaryAt e) = lowExponentAt e b := by
  rw [signalAt_eq, lowExponentAt_eq]
  dsimp [boundaryAt]
  ring
end RH.Transport.TunedCandidate
