-- Prove2me | solution 1 for RH.Transport.LocalBounds.good_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:08.977343+00:00
-- url     : https://prove2.me/submissions/296fb694-f025-42f6-b70b-fa229a8c984e

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z ≤ goodCap p := by
  cases term <;> dsimp [goodPower, goodCap, boundary] at * <;> linarith
end RH.Transport.LocalBounds
