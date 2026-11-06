-- Prove2me | solution 1 for RH.Transport.LocalBounds.good_power_lt_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:51.736026+00:00
-- url     : https://prove2.me/submissions/591e666f-8c10-4779-802a-8bb4e7acfb52

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
import Theorems.Thm_RH_Transport_LocalBounds_good_power_le
import Theorems.Thm_RH_Transport_LocalBounds_good_cap_lt_neg_one

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 :=
  lt_of_le_of_lt (good_power_le hp0 hp hs hw hz term)
    (good_cap_lt_neg_one hp)
end RH.Transport.LocalBounds
