-- Prove2me | solution 1 for RH.Transport.LocalBounds.ramified_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:11.841933+00:00
-- url     : https://prove2.me/submissions/20df5a91-4ffb-4a4c-8f6d-a4244c235423

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p s w z : ℝ}
    (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z ≤ ramifiedCap p := by
  cases term <;> dsimp [ramifiedPower, ramifiedCap, boundary] at * <;> linarith
end RH.Transport.LocalBounds
