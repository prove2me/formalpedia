-- Prove2me | solution 1 for RH.Transport.Candidate.p_lt_one_thousandth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:01.628795+00:00
-- url     : https://prove2.me/submissions/496872cf-306d-4797-a4ef-e92e1f11cdde

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution : p < 1 / 1000 := by norm_num [p]
end RH.Transport.Candidate
