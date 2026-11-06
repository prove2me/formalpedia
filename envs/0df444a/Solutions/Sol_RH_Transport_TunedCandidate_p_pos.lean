-- Prove2me | solution 1 for RH.Transport.TunedCandidate.p_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:46.596368+00:00
-- url     : https://prove2.me/submissions/a09fafd3-079f-40f6-876b-8552d7885688

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : 0 < p := by norm_num [p]
end RH.Transport.TunedCandidate
