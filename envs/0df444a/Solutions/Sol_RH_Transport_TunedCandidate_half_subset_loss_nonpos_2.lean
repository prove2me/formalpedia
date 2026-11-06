-- Prove2me | solution 2 for RH.Transport.TunedCandidate.half_subset_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:23.872938+00:00
-- url     : https://prove2.me/submissions/9d7875e1-3c68-43ca-985b-7eb2685b7279

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_half_subset_loss_le

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ 0 := by
  have hm := half_subset_loss_le hd
  linarith
end RH.Transport.TunedCandidate
