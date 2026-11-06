-- Prove2me | solution 1 for RH.Transport.TunedCandidate.signal_intercept_value
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:38.272194+00:00
-- url     : https://prove2.me/submissions/71120fbb-b6ed-4cb7-9f5f-0b0a019a94d9

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution (s : ℝ) :
    signal s = s - 2147607 / 3125000 := by
  norm_num [signal, signalAt, ell, Geometry.ell, lxAt, hAt, b, p]
  ring
