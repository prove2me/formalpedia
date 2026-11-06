-- Prove2me | solution 1 for RH.Transport.Candidate.intermediate_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:07.752295+00:00
-- url     : https://prove2.me/submissions/c354f765-5e4d-47f9-b192-1990cb7227d6

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution : cushion < sideMargin .intermediate := by
  norm_num [cushion, sideMargin, p]
