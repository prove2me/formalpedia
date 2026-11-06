-- Prove2me | solution 1 for RH.Transport.TunedCandidate.boundary_eq_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:48.937161+00:00
-- url     : https://prove2.me/submissions/a3a9ba1b-4ad7-4a6e-a081-c6eed69c28e1

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_boundaryAt_eq_geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : B = Geometry.boundary p :=
  boundaryAt_eq_geometry p
end RH.Transport.TunedCandidate
