-- Prove2me | solution 1 for RH.Transport.TunedCandidate.sideMargin_eq_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:32.891819+00:00
-- url     : https://prove2.me/submissions/c691f3a9-94ce-4892-96b3-2ef174cb3694

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (term : SideCondition) :
    sideMargin term = sideMarginValue term := by
  cases term <;>
    norm_num [sideMargin, sideMarginValue, intermediateExponent, ell,
      Geometry.ell, lx, ly, h, lxAt, lyAt, hAt, b,
      B, boundaryAt, goodTailDecay, p, zeta]
end RH.Transport.TunedCandidate
