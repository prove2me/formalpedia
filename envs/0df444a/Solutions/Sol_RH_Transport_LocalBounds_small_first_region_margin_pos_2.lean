-- Prove2me | solution 2 for RH.Transport.LocalBounds.small_first_region_margin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:28.720888+00:00
-- url     : https://prove2.me/submissions/b4bfc404-a489-4aeb-9843-5b34636e002f

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p : ℝ} (hp : p < 1 / 1000) :
    0 < boundary p - 1 / 2 := by
  dsimp [boundary]
  linarith
end RH.Transport.LocalBounds
