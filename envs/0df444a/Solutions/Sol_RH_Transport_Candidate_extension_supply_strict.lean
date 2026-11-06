-- Prove2me | solution 1 for RH.Transport.Candidate.extension_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:02.340045+00:00
-- url     : https://prove2.me/submissions/cfe8bf8f-b780-4639-a01c-74185df86519

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution : zeta < 5 * ell p - h p := by
  norm_num [zeta, ell, h, p]
