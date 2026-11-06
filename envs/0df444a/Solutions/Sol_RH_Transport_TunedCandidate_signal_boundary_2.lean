-- Prove2me | solution 2 for RH.Transport.TunedCandidate.signal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:00.035353+00:00
-- url     : https://prove2.me/submissions/62fc0ffe-cd4a-48f9-8996-d748a1f08f2e

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_signalAt_boundaryAt

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : signal B = lowExponent :=
  signalAt_boundaryAt ell b
end RH.Transport.TunedCandidate
