-- Prove2me | solution 1 for RH.Transport.Candidate.local_ramified_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:23.026502+00:00
-- url     : https://prove2.me/submissions/2844132b-5982-4b58-9cb6-1a82d5e1fa56

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_LocalBounds_ramified_power_neg


set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 :=
  ramified_power_neg p_lt_one_thousandth hs hw hz term
end RH.Transport.Candidate
