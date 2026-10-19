-- Prove2me | solution 1 for PackingBounds.exists_radial_admissible_of_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/c9defb59-46f0-475b-9146-ce587153321d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_FullAdmissible_quotient_radialization

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
theorem _root_.solution {d : ℕ}
    (f : FullAdmissible d) :
    ∃ g : CohnElkies.Admissible d,
      CohnElkies.quotient g = fullQuotient f := by
  exact ⟨f.radialization, f.quotient_radialization⟩
end PackingBounds
