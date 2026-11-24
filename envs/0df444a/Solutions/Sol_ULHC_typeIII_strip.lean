-- Prove2me | solution 1 for ULHC.typeIII_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:20:14.610836+00:00
-- url     : https://prove2.me/submissions/d7b8c977-dd20-4ffb-b6b5-d8543e4c2bf5

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ σ.n % 2 = 1 := by
  unfold NoTypeIII at h
  push Not at h
  obtain ⟨c, hc, s, hb, hf, hl1, hl2, hn⟩ := h
  refine ⟨⟨c, s, 1⟩, ⟨le_rfl, ⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_, hn⟩, rfl⟩
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hf]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact hc
end ULHC
