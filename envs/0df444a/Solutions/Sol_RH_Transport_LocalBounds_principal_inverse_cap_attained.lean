-- Prove2me | solution 1 for RH.Transport.LocalBounds.principal_inverse_cap_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:24.924712+00:00
-- url     : https://prove2.me/submissions/9a7a03d2-a77b-46a9-8723-d1fb800148c1

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution (p : ℝ) :
    principalPower .inverse (boundary p) (19 / 20) (33 / 200) =
      -boundary p := by
  rfl
end RH.Transport.LocalBounds
