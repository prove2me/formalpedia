-- Prove2me | solution 1 for RH.Transport.TunedCandidate.intermediate_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:01.906506+00:00
-- url     : https://prove2.me/submissions/886f45e4-9f5a-41e0-b5a2-119daedf6452

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_sideMargin_eq_value

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : cushion < sideMargin .intermediate := by
  rw [sideMargin_eq_value]
  norm_num [cushion, sideMarginValue]
end RH.Transport.TunedCandidate
