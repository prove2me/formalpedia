-- Prove2me | solution 1 for ULHC.D_around
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:28.749156+00:00
-- url     : https://prove2.me/submissions/4fde6ca8-9b16-47b8-a755-7167306ed6a7

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_jump
import Theorems.Thm_ULHC_wD_zero_of_not_mem
import Theorems.Thm_ULHC_not_mem_of_endpoint
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
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
namespace ULHC
theorem _root_.solution {a c : Pt} (ha : a ∉ V) (hc : Around a c) : D F H c = D F H a := by
  obtain ⟨x, y⟩ := a
  have z : ∀ e : Edge, (e.p = (x, y) ∨ e.q = (x, y)) → wD F H e = 0 := fun e h =>
    wD_zero_of_not_mem (not_mem_of_endpoint hF ha h) (not_mem_of_endpoint hH ha h)
  have jR := D_jump hF hH (eR (x, y))
  have jU := D_jump hF hH (eU (x, y))
  have jL := D_jump hF hH (eL (x, y))
  rw [z _ (by simp [eR])] at jR
  rw [z _ (by simp [eU])] at jU
  rw [z _ (by simp [eL, Edge.q])] at jL
  simp only [eR, eU, eL, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at jR jU jL
  obtain ⟨c1, c2⟩ := c
  obtain ⟨h1 | h1, h2 | h2⟩ := hc <;> simp only at h1 h2 <;> subst h1 h2 <;> linarith
end ULHC
