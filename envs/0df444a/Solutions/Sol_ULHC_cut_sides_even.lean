-- Prove2me | solution 1 for ULHC.cut_sides_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:57.027495+00:00
-- url     : https://prove2.me/submissions/28189da9-70a5-4be6-adc0-000056178a82

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
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
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (P : Finset Pt) (B : Finset Edge) (hB : ∀ e, e ∈ B ↔ IsEdge V e ∧ Cut P e)
    (c : Pt) (hc : IsCell V c) : sidesIn B c % 2 = 0 := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold sidesIn ind
  simp only [hB, IsEdge, Cut, bot, top, lft, rgt, Edge.q]
  by_cases a : (x, y) ∈ P <;> by_cases b : (x + 1, y) ∈ P <;> by_cases c : (x, y + 1) ∈ P <;>
    by_cases d : (x + 1, y + 1) ∈ P <;> simp_all
end ULHC
