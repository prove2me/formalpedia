-- Prove2me | solution 1 for ULHC.nOn_front_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:34:48.792333+00:00
-- url     : https://prove2.me/submissions/c18ca45f-5e73-43d2-9643-4b5bf4f0a688

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_nOn_eq
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_front_mem_next
import Theorems.Thm_ULHC_front_mem_self
import Theorems.Thm_ULHC_front_not_mem
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution {n j : ℕ} (hj : j + 1 < n) : nOn c s n (front (cellJ c s j) s) = 2 := by
  rw [nOn_eq c s n _ {j, j + 1}]
  · rw [Finset.card_insert_of_notMem (by simp)]; simp
  · intro m _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; push Not at hne
      exact front_not_mem c s (j := j) (m := m) (Ne.symm hne.1) hne.2 h
    · rintro (rfl | rfl)
      · exact front_mem_self c s m
      · exact front_mem_next c s j
  · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
end ULHC
