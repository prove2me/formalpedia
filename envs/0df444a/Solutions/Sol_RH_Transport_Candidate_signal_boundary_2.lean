-- Prove2me | solution 2 for RH.Transport.Candidate.signal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:57.078183+00:00
-- url     : https://prove2.me/submissions/722ba9cc-c3c1-4f82-bf2a-21e0a285d105

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Geometry_lowExponent_eq_signal_boundary


set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution : signal p B = lowExponent p := by
  exact (lowExponent_eq_signal_boundary p).symm
end RH.Transport.Candidate
