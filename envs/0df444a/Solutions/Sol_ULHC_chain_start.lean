-- Prove2me | solution 1 for ULHC.chain_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:41:25.285375+00:00
-- url     : https://prove2.me/submissions/9e987050-dafa-43f2-b3cc-ca4cb6d30e51

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_frame_ne
import Theorems.Thm_ULHC_inter_unique
import Theorems.Thm_ULHC_chain_lat
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_mem_flip_off
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x ∈ G ∧ (x = lat1 c.c c.s ∨ x = lat2 c.c c.s) ∧ back c.c c.s ∈ G ∧
      (front c.c c.s ∈ G ↔ c.n = 1) ∧
      ((lat1 c.c c.s ∈ G ∧ lat2 c.c c.s ∉ G) ∨ (lat2 c.c c.s ∈ G ∧ lat1 c.c c.s ∉ G)) := by
  have hx0 : x ∈ cellE (cellJ c.c c.s 0) := by rw [cellJ_zero]; exact hx
  obtain ⟨_, hxl⟩ := hok 0 hl.2.2.1 x hx0 hxu
  have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [hlu.1, hlu.2]
  have hxlat := chain_lat hl hok hlu hx hxu
  have hne0 : c.c ≠ endCell b := by have := hl.2.2.2.2.2.2.1 0 hl.2.2.1; rwa [cellJ_zero] at this
  have hother : ∀ y ∈ cellE c.c, y ≠ x → (y ∈ flip G (endCell b) ↔ y ∈ G) :=
    fun y hy hyx => mem_flip_off (fun hyu => hyx (inter_unique hne0 hy hyu hx hxu))
  have memc : ∀ y, y = lat1 c.c c.s ∨ y = lat2 c.c c.s ∨ y = back c.c c.s ∨
      y = front c.c c.s → y ∈ cellE c.c := by
    intro y hy; rw [cellE_frame _ c.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨n1, n2, n3, n4, n5, _⟩ := frame_ne c.c c.s
  have hpat := hl.2.2.2.1
  have hl0 := hpat.2.1 0 hl.2.2.1
  have hf0 := hpat.2.2 0 hl.2.2.1
  rw [cellJ_zero] at hl0 hf0
  have hbx : back c.c c.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n1, n2]
  have hfx : front c.c c.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n3, n4]
  refine ⟨hxG, hxlat, ?_, ?_, ?_⟩
  · rw [← hother _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))) hbx]; exact hpat.1
  · rw [← hother _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))) hfx, hf0]
    have hn1 := hl.2.2.1
    constructor
    · intro h; by_contra hn; have := h.2 (by omega); omega
    · intro h; exact ⟨fun h' => by omega, fun h' => by omega⟩
  · rcases hxlat with h | h
    · left; refine ⟨h ▸ hxG, fun h2 => ?_⟩
      have : lat2 c.c c.s ∈ flip G (endCell b) :=
        (hother _ (memc _ (Or.inr (Or.inl rfl))) (fun he => n5 (h ▸ he.symm))).2 h2
      have := hl0.2.1 this; omega
    · right; refine ⟨h ▸ hxG, fun h1 => ?_⟩
      have : lat1 c.c c.s ∈ flip G (endCell b) :=
        (hother _ (memc _ (Or.inl rfl)) (fun he => n5 (he.trans h))).2 h1
      have := hl0.1.1 this; omega
end ULHC
