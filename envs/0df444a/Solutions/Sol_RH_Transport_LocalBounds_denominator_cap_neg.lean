-- Prove2me | solution 1 for RH.Transport.LocalBounds.denominator_cap_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:07.636786+00:00
-- url     : https://prove2.me/submissions/a93387d5-e6a2-48a9-8629-9e8d20327f2e

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p : ℝ} (hp : p < 1 / 1000)
    (term : DenominatorTerm) : denominatorCap term p < 0 := by
  cases term <;> dsimp [denominatorCap, boundary] <;> linarith
end RH.Transport.LocalBounds
