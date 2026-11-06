-- Prove2me | solution 1 for RH.Transport.LocalBounds.ramified_power_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:52.754319+00:00
-- url     : https://prove2.me/submissions/ce542962-9620-4704-8ed1-4399921c5b81

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
import Theorems.Thm_RH_Transport_LocalBounds_ramified_power_le
import Theorems.Thm_RH_Transport_LocalBounds_ramified_cap_neg

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s w z : ℝ}
    (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 :=
  lt_of_le_of_lt (ramified_power_le hp hs hw hz term)
    (ramified_cap_neg hp)
end RH.Transport.LocalBounds
