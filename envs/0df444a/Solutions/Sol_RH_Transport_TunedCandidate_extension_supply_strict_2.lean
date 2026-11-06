-- Prove2me | solution 2 for RH.Transport.TunedCandidate.extension_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:13.865873+00:00
-- url     : https://prove2.me/submissions/269a23a9-0345-4b73-8d5e-b701ff94412d

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : zeta < 5 * ell - h := by
  have hm := all_side_margins_pos SideCondition.strongSupply
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.TunedCandidate
