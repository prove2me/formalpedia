-- Prove2me | solution 1 for RH.Transport.LocalBounds.small_first_region_margin_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:17.291343+00:00
-- url     : https://prove2.me/submissions/b83693d2-eb0a-4a7b-9180-d43037eaf77f

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 1000) :
    0 < boundary p - 1 / 2 := by
  unfold boundary
  linarith
