-- Prove2me | solution 1 for RH.Transport.TunedCandidate.local_ramified_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:38.932347+00:00
-- url     : https://prove2.me/submissions/0da7fc41-d915-400f-a642-c981e6825b3c

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_eq_geometry
import Theorems.Thm_RH_Transport_LocalBounds_ramified_power_neg


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 := by
  rw [boundary_eq_geometry] at hs
  exact ramified_power_neg p_lt_one_thousandth hs hw hz term
end RH.Transport.TunedCandidate
