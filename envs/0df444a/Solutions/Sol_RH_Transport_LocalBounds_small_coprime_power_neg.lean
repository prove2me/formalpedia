-- Prove2me | solution 1 for RH.Transport.LocalBounds.small_coprime_power_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:27.28882+00:00
-- url     : https://prove2.me/submissions/edabccc8-bf04-4c55-a312-d8187a19d47e

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : PrincipalTerm) :
    principalPower term s (1 / 2) (17 / 50) < 0 := by
  cases term <;> dsimp [principalPower, boundary] at * <;> linarith
end RH.Transport.LocalBounds
