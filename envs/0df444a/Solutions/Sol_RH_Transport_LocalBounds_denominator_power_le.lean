-- Prove2me | solution 1 for RH.Transport.LocalBounds.denominator_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:07.063376+00:00
-- url     : https://prove2.me/submissions/3c57336e-d145-4c54-a900-5f6c24848a6b

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s z : ℝ}
    (hs : boundary p ≤ s) (hz : (33 / 200 : ℝ) ≤ z)
    (term : DenominatorTerm) :
    denominatorPower term s z ≤ denominatorCap term p := by
  cases term <;>
    dsimp [denominatorPower, denominatorCap, boundary] at * <;>
    linarith
end RH.Transport.LocalBounds
