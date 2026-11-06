-- Prove2me | solution 1 for RH.Transport.TunedCandidate.p_lt_one_thousandth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:33.504421+00:00
-- url     : https://prove2.me/submissions/281a4b3c-5092-4b4d-88af-522b8b4fce3b

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : p < 1 / 1000 := by norm_num [p]
end RH.Transport.TunedCandidate
