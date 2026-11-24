-- Prove2me | solution 1 for ULHC.inc_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:52.878006+00:00
-- url     : https://prove2.me/submissions/5558d7ac-a415-4c1b-af51-34f17a8b3128

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Edge_p_ne_q
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {e : Edge} {y z u : Pt} (hy : e.p = y ∨ e.q = y) (hz : e.p = z ∨ e.q = z)
    (hne : y ≠ z) (hu : e.p = u ∨ e.q = u) : u = y ∨ u = z := by
  have hpq := Edge.p_ne_q e
  rcases hy with hy | hy <;> rcases hz with hz | hz <;> rcases hu with hu | hu <;>
    subst hy <;> first
    | exact absurd hz.symm hne
    | exact absurd hz hne
    | exact Or.inl hu.symm
    | exact Or.inr (hu.symm.trans hz)
end ULHC
