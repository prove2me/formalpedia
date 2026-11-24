-- Prove2me | solution 1 for ULHC.alt_iff_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:46.874113+00:00
-- url     : https://prove2.me/submissions/3ac922a8-fd96-432f-8bdc-6658b9d7b205

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
import Theorems.Thm_ULHC_outArc_eq
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
namespace ULHC
theorem _root_.solution (F : Finset Edge) (c : Pt) :
    Alt F c ↔ Source F c ∨ Sink F c := by
  have hs : ∀ s, outArc F c s = _ := outArc_eq F c
  unfold Alt Source Sink
  have e : ∀ P : Side → Bool, (∀ s, P s = true) ↔
      (P .b = true ∧ P .t = true ∧ P .l = true ∧ P .r = true) := by
    intro P; constructor
    · intro h; exact ⟨h _, h _, h _, h _⟩
    · rintro ⟨h1, h2, h3, h4⟩ s; cases s <;> assumption
  have e' : ∀ P : Side → Bool, (∀ s, P s = false) ↔
      (P .b = false ∧ P .t = false ∧ P .l = false ∧ P .r = false) := by
    intro P; constructor
    · intro h; exact ⟨h _, h _, h _, h _⟩
    · rintro ⟨h1, h2, h3, h4⟩ s; cases s <;> assumption
  rw [e, e']
  simp only [hs, Side.horiz, sideEdge, ite_true, ite_false, Bool.false_eq_true]
  cases par c <;>
    by_cases hb : bot c ∈ F <;> by_cases ht : top c ∈ F <;>
    by_cases hl : lft c ∈ F <;> by_cases hr : rgt c ∈ F <;> simp [hb, ht, hl, hr]
end ULHC
