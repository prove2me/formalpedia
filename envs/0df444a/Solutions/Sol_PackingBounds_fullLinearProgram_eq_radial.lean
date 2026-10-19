-- Prove2me | solution 1 for PackingBounds.fullLinearProgram_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/2ab0dbd5-fe19-419f-831d-51f18d3438a2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
import Theorems.Thm_PackingBounds_fullQuotientSet_eq_radial
attribute [local simp] SpherePacking.Alternative.schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_zero

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
    fullLinearProgram d = CohnElkies.linearProgram d := by
  simp only [fullLinearProgram, CohnElkies.linearProgram,
    fullQuotientSet_eq_radial]
end PackingBounds
