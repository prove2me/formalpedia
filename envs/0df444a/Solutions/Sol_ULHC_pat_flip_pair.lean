-- Prove2me | solution 1 for ULHC.pat_flip_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:04.836684+00:00
-- url     : https://prove2.me/submissions/6ff8e0a6-53ac-430a-807e-3579cdc9331b

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_not_mem
import Theorems.Thm_ULHC_front_not_mem
import Theorems.Thm_ULHC_front_mem_next
import Theorems.Thm_ULHC_back_not_mem
import Theorems.Thm_ULHC_APair_flip
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
variable {F : Finset Edge} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution {k : ℕ} (hk : k % 2 = 0) (h : StripPat F c s (k + 3)) :
    StripPat (flip (flip F (cellJ c s (k + 2))) (cellJ c s (k + 1))) c s (k + 1) := by
  obtain ⟨hb, hl, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_flip_iff, mem_flip_iff]
    have := back_not_mem c s (m := k + 2) (by omega)
    have := back_not_mem c s (m := k + 1) (by omega)
    tauto
  · intro j hj
    have e1 := lat1_not_mem c s (j := j) (m := k + 2) (by omega)
    have e2 := lat2_not_mem c s (j := j) (m := k + 2) (by omega)
    have e3 := lat1_not_mem c s (j := j) (m := k + 1) (by omega)
    have e4 := lat2_not_mem c s (j := j) (m := k + 1) (by omega)
    rw [mem_flip_iff, mem_flip_iff, mem_flip_iff, mem_flip_iff]
    have := hl j (by omega)
    tauto
  · intro j hj
    rw [mem_flip_iff, mem_flip_iff]
    rcases (show j < k ∨ j = k by omega) with hjk | rfl
    · have e1 := front_not_mem c s (j := j) (m := k + 2) (by omega) (by omega)
      have e2 := front_not_mem c s (j := j) (m := k + 1) (by omega) (by omega)
      have := hf j (by omega)
      have q1 : j + 1 < k + 3 := by omega
      have q2 : j + 1 < k + 1 := by omega
      simp only [q1, q2, iff_true] at this ⊢
      tauto
    · have e1 := front_not_mem c s (j := j) (m := j + 2) (by omega) (by omega)
      have e2 := front_mem_next c s j
      have := hf j (by omega)
      have q1 : j + 1 < j + 3 := by omega
      simp only [q1, iff_true, hk, lt_self_iff_false, iff_false] at this ⊢
      simp only [zero_ne_one, not_false_eq_true, iff_true] at this ⊢
      tauto
end ULHC
