-- Prove2me | solution 1 for ULHC.pot_jump_v
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:11.034991+00:00
-- url     : https://prove2.me/submissions/2df8449f-bda8-4a92-b25b-47e678482885

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
import Theorems.Thm_ULHC_pot_eq_sum_ite
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
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (hS : Supp E w) (c : Pt) :
    pot E w c - pot E w (c.1 - 1, c.2) = w ⟨.v, c⟩ := by
  rw [pot_eq_sum_ite, pot_eq_sum_ite, ← Finset.sum_sub_distrib]
  have key : ∀ e ∈ E,
      ((if RowSel c e then w e else 0) - if RowSel (c.1 - 1, c.2) e then w e else 0)
        = if e = ⟨.v, c⟩ then w e else 0 := by
    intro e _
    obtain ⟨d, a, b⟩ := e
    obtain ⟨x, y⟩ := c
    cases d <;> simp only [RowSel, Edge.mk.injEq, Prod.mk.injEq] <;> split_ifs <;>
      simp_all <;> omega
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hS _ h).symm
end ULHC
