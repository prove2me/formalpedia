-- Prove2me | solution 2 for RH.Transport.Candidate.subset_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:18.962127+00:00
-- url     : https://prove2.me/submissions/4e17fde8-9c3f-4cb4-94ef-fd023f56bd03

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_p_pos
import Theorems.Thm_RH_Transport_Candidate_p_lt_one_thirtieth
import Theorems.Thm_RH_Transport_Geometry_subsetLoss_nonpos


set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ ell p) :
    subsetLoss p d ≤ 0 :=
  subsetLoss_nonpos p_pos p_lt_one_thirtieth hd0 hd
end RH.Transport.Candidate
