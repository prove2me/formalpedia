-- Prove2me | solution 1 for RH.Transport.TunedCandidate.boundaryAt_eq_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:19.649724+00:00
-- url     : https://prove2.me/submissions/146f55ff-d197-4530-9da7-95a340e795bd

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (p : ℝ) :
    boundaryAt (Geometry.ell p) = Geometry.boundary p := by
  dsimp [boundaryAt, Geometry.ell, Geometry.boundary]
  ring
end RH.Transport.TunedCandidate
