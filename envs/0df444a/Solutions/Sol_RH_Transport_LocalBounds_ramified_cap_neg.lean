-- Prove2me | solution 1 for RH.Transport.LocalBounds.ramified_cap_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:12.423686+00:00
-- url     : https://prove2.me/submissions/4fa9c94a-9d12-4e72-9d17-5f1f09da6289

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p : ℝ} (hp : p < 1 / 1000) :
    ramifiedCap p < 0 := by
  dsimp [ramifiedCap]
  linarith
end RH.Transport.LocalBounds
