-- Prove2me | solution 1 for ULHC.planar_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:12.17763+00:00
-- url     : https://prove2.me/submissions/44544f64-36cc-43bd-b337-eb31039d90df

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_planar_b
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_GridIso_conn_iff
import Theorems.Thm_ULHC_GridIso_mem_image_iff
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (G : Finset Edge) (c : Pt) (h1 : lat1 c .l ∉ G) (h2 : back c .l ∉ G)
    (h3 : Conn G (front1 c .l) (back2 c .l)) (h4 : Conn G (front2 c .l) (back1 c .l))
    (h5 : ¬ Conn G (back1 c .l) (front1 c .l)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  set I := transposeIso
  set G' := G.image I.g
  have m : ∀ e, I.g e ∈ G' ↔ e ∈ G := fun e => I.mem_image_iff
  have cn : ∀ u v, Conn G' (I.f u) (I.f v) ↔ Conn G u v := fun u v => I.conn_iff
  have fP : ∀ p : Pt, I.f p = (p.2, p.1) := fun _ => rfl
  apply planar_b G' (y, x)
  · have : lat1 (y, x) .b = I.g (bot (x, y)) := by simp [lat1, lft, bot, I, transposeIso, tE, tP]
    rw [this, m]; exact h1
  · have : back (y, x) .b = I.g (rgt (x, y)) := by
      simp [back, sideEdge, Side.opp, top, rgt, I, transposeIso, tE, tP]
    rw [this, m]; exact h2
  · simp only [front1, back2]
    rw [show ((y, x) : Pt) = I.f (x, y) from rfl, show ((y + 1, x + 1) : Pt) = I.f (x + 1, y + 1)
      from rfl, cn]; exact h3
  · simp only [front2, back1]
    rw [show ((y + 1, x) : Pt) = I.f (x, y + 1) from rfl, show ((y, x + 1) : Pt) = I.f (x + 1, y)
      from rfl, cn]; exact h4
  · simp only [back1, front1]
    rw [show ((y, x + 1) : Pt) = I.f (x + 1, y) from rfl, show ((y, x) : Pt) = I.f (x, y)
      from rfl, cn]; exact h5
end ULHC
