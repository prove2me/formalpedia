-- Prove2me | solution 1 for RH.Transport.TunedCandidate.support_decay_absorbs_row_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:30.709204+00:00
-- url     : https://prove2.me/submissions/fd070c84-090a-4ec4-8d91-415396b20611

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thirtieth
import Theorems.Thm_RH_Transport_SupportedMass_support_decay_absorbs_row_loss


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {d Z C mass : ℝ}
    (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * ell - 1 + d) / 8) ≤ C :=
  SupportedMass.support_decay_absorbs_row_loss
    p_lt_one_thirtieth hd hZ hC hmass
end RH.Transport.TunedCandidate
