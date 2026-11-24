-- Prove2me | solution 1 for ULHC.frame_of_allConn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:32:46.61349+00:00
-- url     : https://prove2.me/submissions/8dfc5dbd-5a2d-436e-934d-b819b894aad4

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_PStep_symm
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} (h : AllConn F d) (tf : Side) :
    Conn F (back1 d tf) (back2 d tf) ∧ Conn F (back1 d tf) (front1 d tf) ∧
      Conn F (back1 d tf) (front2 d tf) := by
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [back1, back2, front1, front2] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    first
    | exact h1 | exact h2 | exact h3 | exact h1.symm | exact h2.symm | exact h3.symm
    | exact h2.symm.trans h1 | exact h2.symm.trans h3 | exact h1.symm.trans h2
    | exact h1.symm.trans h3
end ULHC
