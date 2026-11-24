-- Prove2me | solution 1 for ULHC.notTypeIII_of_corners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:57.839069+00:00
-- url     : https://prove2.me/submissions/8af9e4d7-61ab-4b94-9cce-4ffda9a64fcd

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
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {d : Pt}
    (h : Conn F d (d.1 + 1, d.2) ∧ Conn F d (d.1, d.2 + 1) ∧ Conn F d (d.1 + 1, d.2 + 1)) :
    NotTypeIII V F d := by
  intro tf _ _ _ _
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [back1, front1] at * <;>
    first
    | exact h2 | exact h1 | exact h2.symm.trans h3 | exact h1.symm.trans h3
    | exact h2.symm.trans h1 | exact h1.symm.trans h2 | exact h2.symm | exact h1.symm
end ULHC
