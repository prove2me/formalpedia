-- Prove2me | solution 1 for RH.Transport.TunedCandidate.half_subset_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:11.695391+00:00
-- url     : https://prove2.me/submissions/0eca326a-70bb-4b1b-bb5b-2ed94ea2c5fb

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thirtieth
import Theorems.Thm_RH_Transport_Geometry_positive_part_le_subset


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ -3 * d / 8 := by
  have hm := Geometry.positive_part_le_subset p_lt_one_thirtieth hd
  change max 0 (5 * ell - 1 + d) ≤ d at hm
  linarith
end RH.Transport.TunedCandidate
