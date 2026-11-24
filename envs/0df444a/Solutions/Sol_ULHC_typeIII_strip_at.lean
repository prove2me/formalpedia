-- Prove2me | solution 1 for ULHC.typeIII_strip_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:44:46.13387+00:00
-- url     : https://prove2.me/submissions/18a8d956-30e0-4171-b038-a5ee4baa1d16

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {d : Pt} (hd : IsCell V d)
    (h : ¬ NotTypeIII V F d) : ∃ σ : StripSpec, σ.c = d ∧ ValidStrip V F σ ∧ σ.n % 2 = 1 := by
  simp only [NotTypeIII, not_forall] at h
  obtain ⟨s, hb, hf, hl1, hl2, hn⟩ := h
  refine ⟨⟨d, s, 1⟩, rfl, ⟨le_rfl, ⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_, hn⟩, rfl⟩
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hf]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact hd
end ULHC
