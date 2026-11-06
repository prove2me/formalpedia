-- Prove2me | solution 1 for RH.Transport.Candidate.central_remaining_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:06.927201+00:00
-- url     : https://prove2.me/submissions/5f45da5e-d35a-42e7-a9c0-c2c5e6b8d522

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]
