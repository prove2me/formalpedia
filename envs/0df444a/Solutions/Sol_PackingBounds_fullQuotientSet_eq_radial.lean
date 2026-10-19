-- Prove2me | solution 1 for PackingBounds.fullQuotientSet_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/07fd246b-7894-4b8e-9690-79cc324cb0c2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_fullQuotientSet_eq_radial_iff
import Theorems.Thm_PackingBounds_exists_radial_admissible_of_full

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
theorem _root_.solution (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d := by
  apply (fullQuotientSet_eq_radial_iff d).2
  exact exists_radial_admissible_of_full
end PackingBounds
