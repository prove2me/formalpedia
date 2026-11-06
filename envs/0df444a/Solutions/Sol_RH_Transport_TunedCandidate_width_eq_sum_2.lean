-- Prove2me | solution 2 for RH.Transport.TunedCandidate.width_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:50.079663+00:00
-- url     : https://prove2.me/submissions/ccf46a7c-a615-445a-99c0-80972478988a

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_widthAt_eq_sum

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : width = lx + ly := widthAt_eq_sum ell b
end RH.Transport.TunedCandidate
