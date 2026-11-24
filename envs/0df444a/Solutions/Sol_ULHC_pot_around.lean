-- Prove2me | solution 1 for ULHC.pot_around
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:37.92591+00:00
-- url     : https://prove2.me/submissions/0f2935e1-d29b-4737-ae86-5d14e8208721

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_pot_jump
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ} (hS : Supp E w) (hb : Balanced w)
include hS hb
namespace ULHC
theorem _root_.solution {z : Pt} (h0 : w (eR z) = 0 ∧ w (eU z) = 0 ∧ w (eL z) = 0 ∧ w (eD z) = 0)
    {c : Pt} (hc : Around z c) : pot E w c = pot E w z := by
  obtain ⟨x, y⟩ := z
  have jR := pot_jump hS hb (eR (x, y))
  have jU := pot_jump hS hb (eU (x, y))
  have jL := pot_jump hS hb (eL (x, y))
  rw [h0.1] at jR
  rw [h0.2.1] at jU
  rw [h0.2.2.1] at jL
  simp only [eR, eU, eL, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at jR jU jL
  obtain ⟨c1, c2⟩ := c
  obtain ⟨h1 | h1, h2 | h2⟩ := hc <;> simp only at h1 h2 <;> subst h1 h2 <;> linarith
end ULHC
