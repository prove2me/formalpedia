-- Prove2me | solution 1 for ULHC.back2_ne_front2_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:43.986011+00:00
-- url     : https://prove2.me/submissions/1cff78d0-f3ac-4458-bd97-bbcd74853406

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
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
open Finset
namespace ULHC
theorem _root_.solution (d : Pt) (s : Side) : back2 d s ≠ front2 (nb d s) s := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [back2, front2, nb] <;> omega
end ULHC
