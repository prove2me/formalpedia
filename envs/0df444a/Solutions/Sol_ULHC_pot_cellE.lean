-- Prove2me | solution 1 for ULHC.pot_cellE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:47.568873+00:00
-- url     : https://prove2.me/submissions/fde8158d-db01-4b9b-b959-6a14ac07fcc7

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_pot_eq_sum_ite
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c x : Pt) (f : Edge → ℤ) :
    pot (cellE c) f x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then f (lft c) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then f (rgt c) else 0) := by
  obtain ⟨c1, c2⟩ := c
  rw [pot_eq_sum_ite]
  unfold cellE
  rw [Finset.sum_insert (by simp [bot, top, lft, rgt]),
    Finset.sum_insert (by simp [top, lft, rgt]),
    Finset.sum_insert (by simp [lft, rgt]), Finset.sum_singleton]
  simp [RowSel, bot, top, lft, rgt]
end ULHC
