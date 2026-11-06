-- Prove2me | solution 1 for RH.Transport.TunedCandidate.local_principal_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:42.001405+00:00
-- url     : https://prove2.me/submissions/a9f4f1c4-2b4b-482f-b768-3f64416ae03b

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_p_pos
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_eq_geometry
import Theorems.Thm_RH_Transport_LocalBounds_principal_power_le


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -B := by
  rw [boundary_eq_geometry] at hs ⊢
  exact principal_power_le p_pos p_lt_one_thousandth hs hw hz term
end RH.Transport.TunedCandidate
