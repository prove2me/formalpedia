-- Prove2me | solution 1 for RH.Transport.Candidate.local_good_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:19.72462+00:00
-- url     : https://prove2.me/submissions/9259ebea-9e76-4813-9ff8-c8a41e9b7b95

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_p_pos
import Theorems.Thm_RH_Transport_Candidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_LocalBounds_good_power_lt_neg_one


set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 :=
  good_power_lt_neg_one p_pos p_lt_one_thousandth hs hw hz term
end RH.Transport.Candidate
