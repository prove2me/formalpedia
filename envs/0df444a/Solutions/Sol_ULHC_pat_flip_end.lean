-- Prove2me | solution 1 for ULHC.pat_flip_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:26.527282+00:00
-- url     : https://prove2.me/submissions/670eabf8-2846-4916-b451-175b27fca069

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_not_mem
import Theorems.Thm_ULHC_front_mem_next
import Theorems.Thm_ULHC_front_not_mem
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_not_mem
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (h : StripPat F c s (k + 2)) :
    StripPat (flip F (cellJ c s (k + 1))) c s (k + 1) := by
  obtain ⟨hb, hl, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_flip_iff]; have := back_not_mem c s (m := k + 1) (by omega); tauto
  · intro j hj
    have e1 := lat1_not_mem c s (j := j) (m := k + 1) (by omega)
    have e2 := lat2_not_mem c s (j := j) (m := k + 1) (by omega)
    rw [mem_flip_iff, mem_flip_iff]
    have := hl j (by omega)
    tauto
  · intro j hj
    rw [mem_flip_iff]
    rcases (show j < k ∨ j = k by omega) with hjk | rfl
    · have e := front_not_mem c s (j := j) (m := k + 1) (by omega) (by omega)
      have := hf j (by omega)
      have q1 : j + 1 < k + 2 := by omega
      have q2 : j + 1 < k + 1 := by omega
      simp only [q1, q2, iff_true] at this ⊢
      tauto
    · have e := front_mem_next c s j
      have := hf j (by omega)
      have q1 : j + 1 < j + 2 := by omega
      simp only [q1, iff_true, lt_self_iff_false, iff_false] at this ⊢
      tauto
end ULHC
