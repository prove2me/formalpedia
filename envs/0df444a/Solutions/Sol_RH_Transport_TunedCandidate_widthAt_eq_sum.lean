-- Prove2me | solution 1 for RH.Transport.TunedCandidate.widthAt_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:07.83393+00:00
-- url     : https://prove2.me/submissions/e2d76c6e-b374-4ba0-ab52-7449663de173

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (e b : ℝ) :
    widthAt e = lxAt e b + lyAt e b := by
  dsimp [widthAt, lxAt, lyAt]
  ring
end RH.Transport.TunedCandidate
