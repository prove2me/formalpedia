-- Prove2me | solution 1 for RH.Transport.Candidate.cushion_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:04.76562+00:00
-- url     : https://prove2.me/submissions/a483577d-81da-40c7-9c48-69f51dcf98b7

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution : 0 < cushion := by
  norm_num [cushion]
