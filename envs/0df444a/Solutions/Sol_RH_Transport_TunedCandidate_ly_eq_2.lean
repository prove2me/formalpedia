-- Prove2me | solution 2 for RH.Transport.TunedCandidate.ly_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:58.758196+00:00
-- url     : https://prove2.me/submissions/e86d3ca4-fda0-4478-9222-a540b57ce80f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_lyAt_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : ly = lx + b := lyAt_eq ell b
end RH.Transport.TunedCandidate
