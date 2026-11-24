-- Prove2me | solution 1 for ULHC.Ends.inc_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:36.523854+00:00
-- url     : https://prove2.me/submissions/fd5d49fb-6d60-44db-91d6-c4f9e269ddaa

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
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
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution (h : Ends e u v) (z : Pt) : (e.p = z ∨ e.q = z) ↔ (z = u ∨ z = v) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> constructor <;> rintro (h | h) <;>
    simp_all
end Ends
end ULHC
