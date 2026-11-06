-- Prove2me | solution 1 for RH.Transport.TunedCandidate.local_good_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:31.258323+00:00
-- url     : https://prove2.me/submissions/9f7022e3-a3f3-494d-9118-c9dae19f1cc7

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_p_pos
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_eq_geometry
import Theorems.Thm_RH_Transport_LocalBounds_good_power_lt_neg_one


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 := by
  rw [boundary_eq_geometry] at hs
  exact good_power_lt_neg_one p_pos p_lt_one_thousandth hs hw hz term
end RH.Transport.TunedCandidate
