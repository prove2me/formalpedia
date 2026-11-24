-- Prove2me | solution 1 for ULHC.planar_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:26.552893+00:00
-- url     : https://prove2.me/submissions/d6974a55-e058-49fd-bb05-af5f62e42dc0

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_GridIso_conn_iff
import Theorems.Thm_ULHC_GridIso_mem_image_iff
import Theorems.Thm_ULHC_planar_cell
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (G : Finset Edge) (c : Pt) (h1 : lat1 c .b ∉ G) (h2 : back c .b ∉ G)
    (h3 : Conn G (front1 c .b) (back2 c .b)) (h4 : Conn G (front2 c .b) (back1 c .b))
    (h5 : ¬ Conn G (back1 c .b) (front1 c .b)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  set I := reflectIso
  set G' := G.image I.g
  have m : ∀ e, I.g e ∈ G' ↔ e ∈ G := fun e => I.mem_image_iff
  have cn : ∀ u v, Conn G' (I.f u) (I.f v) ↔ Conn G u v := fun u v => I.conn_iff
  have fP : ∀ p : Pt, I.f p = (p.1, -p.2) := fun _ => rfl
  apply planar_cell G' x (-y - 1)
  · have : bot (x, -y - 1) = I.g (top (x, y)) := by
      simp [bot, top, I, reflectIso, rE, rP]; ring
    rw [this, m]; exact h2
  · have : lft (x, -y - 1) = I.g (lft (x, y)) := by
      simp [lft, I, reflectIso, rE]
    rw [this, m]; exact h1
  · have e1 : ((x + 1, -y - 1) : Pt) = I.f (x + 1, y + 1) := by rw [fP]; simp; ring
    have e2 : ((x, -y - 1 + 1) : Pt) = I.f (x, y) := by rw [fP]; simp
    rw [e1, e2, cn]; exact h3.symm
  · have e1 : ((x + 1, -y - 1 + 1) : Pt) = I.f (x + 1, y) := by rw [fP]; simp
    have e2 : ((x, -y - 1) : Pt) = I.f (x, y + 1) := by rw [fP]; simp; ring
    rw [e1, e2, cn]; exact h4
  · have e1 : ((x, -y - 1) : Pt) = I.f (x, y + 1) := by rw [fP]; simp; ring
    have e2 : ((x + 1, -y - 1) : Pt) = I.f (x + 1, y + 1) := by rw [fP]; simp; ring
    rw [e1, e2, cn]
    intro h'; exact h5 (h'.trans h3.symm)
end ULHC
