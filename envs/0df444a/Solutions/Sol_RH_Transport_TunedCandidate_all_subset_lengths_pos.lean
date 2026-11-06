-- Prove2me | solution 1 for RH.Transport.TunedCandidate.all_subset_lengths_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:21.898464+00:00
-- url     : https://prove2.me/submissions/56086ccb-4cde-48e0-b45a-6552ac712d72

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {d : ℝ} (hd : d ≤ ell) :
    0 < width - 2 * d ∧ 0 < lx - d ∧ 0 < ly - d ∧
      0 < ly - d - 11 * b / 6 := by
  have hM := all_side_margins_pos SideCondition.minimumWidth
  have hx := all_side_margins_pos SideCondition.minimumLx
  have hy := all_side_margins_pos SideCondition.minimumLy
  have hG := all_side_margins_pos SideCondition.gram
  dsimp [sideMargin] at hM hx hy hG
  dsimp [width, widthAt]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
end RH.Transport.TunedCandidate
