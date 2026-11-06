-- Prove2me | solution 1 for RH.Transport.Candidate.lowExponent_value
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:50.510967+00:00
-- url     : https://prove2.me/submissions/bc61eead-5475-4644-8cc5-d44738a58dd5

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution :
    lowExponent p = 299931521 / 1600000000 := by
  norm_num [lowExponent, lx, b, p]
