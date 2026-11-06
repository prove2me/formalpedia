-- Prove2me | solution 1 for RH.Transport.TunedCandidate.half_subset_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:11:22.998199+00:00
-- url     : https://prove2.me/submissions/14d612cb-2845-4500-bddb-c5f7a586ffde

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ 0 := by
  rcases le_total (5 * ell - 1 + d) 0 with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    norm_num [ell, Geometry.ell, p]
    nlinarith
