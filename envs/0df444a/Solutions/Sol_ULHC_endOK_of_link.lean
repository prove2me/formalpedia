-- Prove2me | solution 1 for ULHC.endOK_of_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:42.954335+00:00
-- url     : https://prove2.me/submissions/fb3367fa-f466-4e9e-b7e6-8f6ac84f7272

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Theorems.Thm_ULHC_end_alt
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_mem_flip_off
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} {σ τ : StripSpec} (hl : CR2 V G σ τ) :
    EndOK V G τ := by
  intro hev
  obtain ⟨_, _, hc1, hpatc, hcellc, _, _, hendc, _⟩ := hl
  have h2 : 2 ≤ τ.n := by omega
  obtain ⟨l1, l2, b, f⟩ := end_alt h2 hev hpatc
  have tr : ∀ e ∈ cellE (endCell τ), (e ∈ flip G (endCell σ) ↔ e ∈ G) :=
    fun e he => mem_flip_off (hendc hev e he)
  have mem : ∀ e, e = lat1 (endCell τ) τ.s ∨ e = lat2 (endCell τ) τ.s ∨ e = back (endCell τ) τ.s ∨
      e = front (endCell τ) τ.s → e ∈ cellE (endCell τ) := by
    intro e he; rw [cellE_frame _ τ.s]; rcases he with rfl | rfl | rfl | rfl <;> simp
  refine ⟨hcellc _ (by omega), (tr _ (mem _ (Or.inl rfl))).1 l1,
    (tr _ (mem _ (Or.inr (Or.inl rfl)))).1 l2,
    fun h => b ((tr _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).2 h),
    fun h => f ((tr _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).2 h)⟩
end ULHC
