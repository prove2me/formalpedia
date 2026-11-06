-- Prove2me | solution 2 for RH.Transport.TunedCandidate.h_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:51.392917+00:00
-- url     : https://prove2.me/submissions/58986134-8538-43e3-86d8-6cb9cca5ab93

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_hAt_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : h = 1 - lx + ell := hAt_eq ell b
end RH.Transport.TunedCandidate
