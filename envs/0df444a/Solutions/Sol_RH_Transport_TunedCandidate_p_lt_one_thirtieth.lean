-- Prove2me | solution 1 for RH.Transport.TunedCandidate.p_lt_one_thirtieth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:44.084468+00:00
-- url     : https://prove2.me/submissions/cba0bed4-4d56-418f-a1ea-69d7cf40041f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : p < 1 / 30 := by norm_num [p]
end RH.Transport.TunedCandidate
