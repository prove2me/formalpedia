-- Prove2me | solution 1 for RH.Transport.TunedCandidate.all_side_margins_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:13.560599+00:00
-- url     : https://prove2.me/submissions/72692801-d218-4e7b-8b32-38c287906140

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_sideMargin_eq_value

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (term : SideCondition) : 0 < sideMargin term := by
  rw [sideMargin_eq_value]
  cases term <;> norm_num [sideMarginValue]
end RH.Transport.TunedCandidate
