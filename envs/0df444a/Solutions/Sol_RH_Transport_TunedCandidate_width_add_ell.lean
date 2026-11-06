-- Prove2me | solution 1 for RH.Transport.TunedCandidate.width_add_ell
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:45.00001+00:00
-- url     : https://prove2.me/submissions/17b46eb2-07cb-48da-8e29-586a982c8525

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_Geometry_width_add_ell

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : width + ell = 1 := by
  unfold width widthAt ell
  have h := Geometry.width_add_ell p
  unfold Geometry.width Geometry.ell at h
  linarith
