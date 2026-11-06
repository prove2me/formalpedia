-- Prove2me | solution 2 for RH.Transport.TunedCandidate.selected_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:13.158199+00:00
-- url     : https://prove2.me/submissions/9ebb4daf-2106-4cb8-af6e-af58d549b234

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : (7 / 37 : ℝ) < ell / (h + zeta) := by
  have hm := all_side_margins_pos SideCondition.selectedSupply
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.TunedCandidate
