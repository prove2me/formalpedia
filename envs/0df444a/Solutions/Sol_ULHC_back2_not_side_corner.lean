-- Prove2me | solution 1 for ULHC.back2_not_side_corner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:36.4773+00:00
-- url     : https://prove2.me/submissions/cac6ba0a-ec16-45e8-8b39-03e92660235a

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution :
    back2 c s ∉ ({back1 (nb c (latA s)) s, back2 (nb c (latA s)) s, front1 (nb c (latA s)) s,
      front2 (nb c (latA s)) s} : Finset Pt) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, back2, front1, front2, latA, nb] <;> omega
end ULHC
