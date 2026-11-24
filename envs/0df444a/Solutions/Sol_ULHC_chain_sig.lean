-- Prove2me | solution 1 for ULHC.chain_sig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:27.276584+00:00
-- url     : https://prove2.me/submissions/7fa807f8-c4ef-4ef9-b95a-c61767b6b8ef

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_strip_sig
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
theorem _root_.solution {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c) :
    SigFrom G c.c c.s c.n 1 := by
  intro i hi hin
  have hoff : ∀ x ∈ cellE (cellJ c.c c.s i), (x ∈ flip G (endCell b) ↔ x ∈ G) := by
    intro x hx
    refine mem_flip_off (fun hxu => ?_)
    have := (hok i hin x hx hxu).1; omega
  have hsig := strip_sig hl.2.2.2.1 hin
  have mem : ∀ y, y = lat1 (cellJ c.c c.s i) c.s ∨ y = lat2 (cellJ c.c c.s i) c.s ∨
      y = back (cellJ c.c c.s i) c.s ∨ y = front (cellJ c.c c.s i) c.s →
      y ∈ cellE (cellJ c.c c.s i) := by
    intro y hy; rw [cellE_frame _ c.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨g1, g2, gb, gf⟩ := hsig
  rw [hoff _ (mem _ (Or.inl rfl))] at g1
  rw [hoff _ (mem _ (Or.inr (Or.inl rfl)))] at g2
  rw [hoff _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))] at gb
  rw [hoff _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))] at gf
  exact ⟨g1, g2, gb, gf⟩
end ULHC
