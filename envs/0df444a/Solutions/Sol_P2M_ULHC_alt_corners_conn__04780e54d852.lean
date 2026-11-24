-- Prove2me | solution 1 for P2M_ULHC_alt_corners_conn__04780e54d852
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:44.073912+00:00
-- url     : https://prove2.me/submissions/04db5ddd-337d-438d-8345-62eff0b9d036

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_Conn_of_edge
import Theorems.Thm_ULHC_Conn_trans
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
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {r : Pt} (hT : NotTypeIII V F r)
    (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) := by
  obtain ⟨x, y⟩ := r
  rcases ha with ⟨hb, ht, hl, hr'⟩ | ⟨hb, ht, hl, hr'⟩
  · have h := hT .t hb ht hl hr'
    simp only [back1, front1] at h
    have e1 : Conn F (x, y) (x + 1, y) := Conn.of_edge hb
    have e2 : Conn F (x, y + 1) (x + 1, y + 1) := Conn.of_edge ht
    exact ⟨e1, h, h.trans e2⟩
  · have h := hT .r hl hr' hb ht
    simp only [back1, front1] at h
    have e1 : Conn F (x, y) (x, y + 1) := Conn.of_edge hl
    have e2 : Conn F (x + 1, y) (x + 1, y + 1) := Conn.of_edge hr'
    exact ⟨h, e1, h.trans e2⟩
end ULHC
