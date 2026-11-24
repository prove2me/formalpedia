-- Prove2me | solution 1 for ULHC.pot_jump_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:59.810259+00:00
-- url     : https://prove2.me/submissions/0fbbe125-77b7-4a81-8bec-44cfde38f893

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
import Theorems.Thm_ULHC_pot_jump_v
import Theorems.Thm_ULHC_exists_left_bound
import Theorems.Thm_ULHC_pot_eq_zero_of_left
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
theorem _root_.solution (hS : Supp E w) (hbal : Balanced w) (c : Pt) :
    pot E w c - pot E w (c.1, c.2 - 1) = w ⟨.h, c⟩ := by
  obtain ⟨B, hB⟩ := exists_left_bound E
  obtain ⟨x, y⟩ := c
  let f : ℤ → ℤ := fun x => pot E w (x, y) - pot E w (x, y - 1) - w ⟨.h, (x, y)⟩
  have base : ∀ x, x ≤ B → f x = 0 := by
    intro x hx
    have h1 := pot_eq_zero_of_left (w := w) hB (x, y) hx
    have h2 := pot_eq_zero_of_left (w := w) hB (x, y - 1) hx
    have h3 : w ⟨.h, (x, y)⟩ = 0 := by
      apply hS
      intro hm
      have := hB _ hm
      simp at this
      omega
    simp only [f, h1, h2, h3]; ring
  have step : ∀ x, f x = f (x - 1) := by
    intro x
    have j1 := pot_jump_v hS (x, y)
    have j2 := pot_jump_v hS (x, y - 1)
    have hb := hbal (x, y)
    simp only [eD, eR, eL, eU] at hb
    simp only at j1 j2
    simp only [f]
    linarith
  have up : ∀ x, B ≤ x → f x = 0 := by
    intro x hx
    induction x, hx using Int.leInduction with
    | base => exact base B le_rfl
    | succ n _ ih =>
      rw [step (n + 1)]
      simp only [add_sub_cancel_right]
      exact ih
  have all : ∀ x, f x = 0 := by
    intro x
    rcases le_total x B with hx | hx
    · exact base x hx
    · exact up x hx
  have := all x
  simp only [f] at this
  simp only
  linarith
end ULHC
