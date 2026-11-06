-- Prove2me | solution 1 for RH.Transport.LocalBounds.principal_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:03.487215+00:00
-- url     : https://prove2.me/submissions/4290183e-76d8-4368-a356-25d22a83bf44

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
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -boundary p := by
  cases term <;> dsimp [principalPower, boundary] at * <;> linarith
end RH.Transport.LocalBounds
