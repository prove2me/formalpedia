-- Prove2me | solution 1 for ULHC.flowL_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:27:41.266369+00:00
-- url     : https://prove2.me/submissions/b7e9f7e5-f3c0-4dcf-86a0-23b4ca98c2b4

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_eq_of_ends
import Theorems.Thm_ULHC_Adj_ends
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_stepFlow_ne_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {G : Finset Edge}
namespace ULHC
theorem _root_.solution {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l)) {e : Edge}
    (h : flowL u l e ≠ 0) : e ∈ G := by
  induction l generalizing u with
  | nil => simp [flowL] at h
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    simp only [flowL] at h
    by_cases h1 : stepFlow u v e = 0
    · rw [h1, zero_add] at h; exact ih hc.2 h
    · obtain ⟨e0, he0, h0⟩ := hc.1.ends
      have : e = e0 := Edge.eq_of_ends (stepFlow_ne_zero h1) h0
      rw [this]; exact he0
end ULHC
