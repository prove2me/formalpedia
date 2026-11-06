-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:24.482198+00:00
-- url     : https://prove2.me/submissions/9ba5cfbc-dcc9-430d-bf39-b1a334cf448f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_signalAt_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (s : ℝ) : signal s = s - 2 / 3 - b / 6 :=
  signalAt_eq ell b s
end RH.Transport.TunedCandidate
