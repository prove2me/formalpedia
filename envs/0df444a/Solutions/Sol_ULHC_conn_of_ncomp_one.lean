-- Prove2me | solution 1 for ULHC.conn_of_ncomp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:19.504193+00:00
-- url     : https://prove2.me/submissions/b60e0b36-c4f5-4f93-8e75-0bb5e9e59ca4

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_cls_self
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {H : Finset Edge} (h1 : ncomp V H = 1) {x y : Pt}
    (hx : x ∈ V) (hy : y ∈ V) : Conn H x y := by
  unfold ncomp at h1
  obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
  have ex : cls V H x ∈ V.image (cls V H) := Finset.mem_image_of_mem _ hx
  have ey : cls V H y ∈ V.image (cls V H) := Finset.mem_image_of_mem _ hy
  rw [hS, Finset.mem_singleton] at ex ey
  have : y ∈ cls V H x := by rw [ex, ← ey]; exact mem_cls_self hy
  simp only [cls, Finset.mem_filter] at this
  exact this.2
end ULHC
