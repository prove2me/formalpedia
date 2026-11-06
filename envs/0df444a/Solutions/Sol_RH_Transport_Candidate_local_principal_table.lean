-- Prove2me | solution 1 for RH.Transport.Candidate.local_principal_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:23.860603+00:00
-- url     : https://prove2.me/submissions/16c99f87-50e1-449a-ab6e-0ef9f406686d

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_p_pos
import Theorems.Thm_RH_Transport_Candidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_LocalBounds_principal_power_le


set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -B :=
  principal_power_le p_pos p_lt_one_thousandth hs hw hz term
end RH.Transport.Candidate
