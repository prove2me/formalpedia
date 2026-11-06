-- Prove2me | solution 2 for RH.Transport.TunedCandidate.small_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:12.440199+00:00
-- url     : https://prove2.me/submissions/271c7fd0-fdfb-4905-9dda-7195fdee9b9b

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_sideMargin_eq_value

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : cushion < sideMargin .small := by
  rw [sideMargin_eq_value]
  norm_num [cushion, sideMarginValue]
end RH.Transport.TunedCandidate
