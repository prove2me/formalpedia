-- Prove2me | solution 1 for RH.Transport.LocalBounds.small_ramified_power_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:28.001852+00:00
-- url     : https://prove2.me/submissions/63197902-9097-4dc8-b151-37dd2dcfbcaa

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : SmallRamifiedTerm) :
    smallRamifiedPower term s ≤ 1 / 2 := by
  cases term <;> dsimp [smallRamifiedPower, boundary] at * <;> linarith
end RH.Transport.LocalBounds
