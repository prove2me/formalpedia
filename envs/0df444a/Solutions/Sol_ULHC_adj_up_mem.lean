-- Prove2me | solution 1 for ULHC.adj_up_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:55.17047+00:00
-- url     : https://prove2.me/submissions/1734c796-f826-4d1b-a02f-9ab8bc393723

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
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
theorem _root_.solution {G : Finset Edge} {x y : ℤ} (h : Adj G (x, y + 1) (x, y)) :
    lft (x, y) ∈ G := by
  obtain ⟨⟨d, p1, p2⟩, he, h⟩ := h
  cases d <;> rcases h with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
    simp only [Edge.q, Prod.mk.injEq] at q1 q2 <;> try omega
  all_goals (obtain ⟨rfl, rfl⟩ : p1 = x ∧ p2 = y := by omega); exact he
end ULHC
