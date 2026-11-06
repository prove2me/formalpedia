-- Prove2me | solution 2 for RH.Transport.TunedCandidate.buffered_upper_scale_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:14.632794+00:00
-- url     : https://prove2.me/submissions/006b4fff-c4f1-40dc-96b9-f9e937a749f6

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : h + zeta < 1 := by
  have hm := all_side_margins_pos SideCondition.bufferedUpperScale
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.TunedCandidate
