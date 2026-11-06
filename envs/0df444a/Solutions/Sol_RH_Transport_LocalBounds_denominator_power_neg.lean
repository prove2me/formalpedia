-- Prove2me | solution 1 for RH.Transport.LocalBounds.denominator_power_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:22.816976+00:00
-- url     : https://prove2.me/submissions/16f51782-eaa9-43e0-bdaa-17fcc71ce707

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
import Theorems.Thm_RH_Transport_LocalBounds_denominator_power_le
import Theorems.Thm_RH_Transport_LocalBounds_denominator_cap_neg

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s z : ℝ} (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hz : (33 / 200 : ℝ) ≤ z)
    (term : DenominatorTerm) : denominatorPower term s z < 0 :=
  lt_of_le_of_lt (denominator_power_le hs hz term)
    (denominator_cap_neg hp term)
end RH.Transport.LocalBounds
