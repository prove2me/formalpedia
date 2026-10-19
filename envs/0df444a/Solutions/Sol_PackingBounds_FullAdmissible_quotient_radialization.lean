-- Prove2me | solution 1 for PackingBounds.FullAdmissible.quotient_radialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/a66da315-3cab-4554-827e-a8c980f2f57b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_IsUnrestrictedAdmissible_quotient_radialSymmetrization

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
open PackingBounds
namespace PackingBounds
namespace FullAdmissible
theorem _root_.solution {d : ℕ}
    (f : FullAdmissible d) :
    CohnElkies.quotient f.radialization = fullQuotient f := by
  change
    SpherePacking.Alternative.quotient
        (SpherePacking.Alternative.radialSymmetrization f.function) =
      SpherePacking.Alternative.quotient f.function
  exact f.toAlternative.quotient_radialSymmetrization
end FullAdmissible
end PackingBounds
