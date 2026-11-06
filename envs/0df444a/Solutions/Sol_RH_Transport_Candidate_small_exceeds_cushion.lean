-- Prove2me | solution 1 for RH.Transport.Candidate.small_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:06.203982+00:00
-- url     : https://prove2.me/submissions/edea1e4c-ed70-4412-bed9-bb4d95ff7067

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution :
    cushion < sideMargin .small := by
  norm_num [cushion, sideMargin, p]
