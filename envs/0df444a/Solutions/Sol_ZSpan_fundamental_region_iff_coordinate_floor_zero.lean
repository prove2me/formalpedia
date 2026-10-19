-- Prove2me | solution 1 for ZSpan.fundamental_region_iff_coordinate_floor_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/87055226-1c9c-4c55-bb4b-f50a55563ae8

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open ZSpan
variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]
namespace ZSpan
theorem _root_.solution (v : E) : v ∈ fundamentalDomain b ↔ floor b v = 0 := by
  simp_rw [mem_fundamentalDomain, ← Int.floor_eq_zero_iff]
  constructor <;> intro h
  · simp [floor, h]
  · intro i
    exact_mod_cast (by simpa [h] using! (repr_floor_apply b v i).symm)
end ZSpan
