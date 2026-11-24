-- Prove2me | solution 1 for ULHC.wD_balanced_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:58.210297+00:00
-- url     : https://prove2.me/submissions/0536b5f8-9e08-47c9-aae2-41f840a5efdc

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_par_sub_fst
import Theorems.Thm_ULHC_par_sub_snd
import Theorems.Thm_ULHC_par_sub_sub
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (F H : Finset Edge) (p : Pt) (hdeg : deg F p = deg H p) :
    wD F H (eD p) + wD F H (eR p) = wD F H (eL p) + wD F H (eU p) := by
  obtain ⟨x, y⟩ := p
  have p1 := par_sub_sub (x, y)
  have p2 := par_sub_snd (x, y)
  have p3 := par_sub_fst (x, y)
  simp only at p1 p2 p3
  unfold deg ind at hdeg
  unfold wD
  simp only [up, inE1, eD, eR, eL, eU, Edge.lo, p1, p2, p3] at hdeg ⊢
  cases par (x, y) <;>
  by_cases a1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ F <;>
  by_cases a2 : (⟨.h, (x, y)⟩ : Edge) ∈ F <;>
  by_cases a3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ F <;>
  by_cases a4 : (⟨.v, (x, y)⟩ : Edge) ∈ F <;>
  by_cases b1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ H <;>
  by_cases b2 : (⟨.h, (x, y)⟩ : Edge) ∈ H <;>
  by_cases b3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ H <;>
  by_cases b4 : (⟨.v, (x, y)⟩ : Edge) ∈ H <;>
  simp [a1, a2, a3, a4, b1, b2, b3, b4, wb] at hdeg ⊢
end ULHC
