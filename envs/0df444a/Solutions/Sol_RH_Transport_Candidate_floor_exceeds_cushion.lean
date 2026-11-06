-- Prove2me | solution 1 for RH.Transport.Candidate.floor_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:44.757871+00:00
-- url     : https://prove2.me/submissions/d4714cfe-caac-44fb-83d3-95527ce4c5b8

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution :
    cushion - 2 * zeta < sideMargin .floor - 2 * zeta := by
  norm_num [cushion, zeta, sideMargin, p]
