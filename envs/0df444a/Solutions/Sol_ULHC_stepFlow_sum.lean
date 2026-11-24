-- Prove2me | solution 1 for ULHC.stepFlow_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:27:50.88041+00:00
-- url     : https://prove2.me/submissions/9bf5b80e-92e9-4f51-ab0f-a2a096912ac0

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_eq_of_ends
import Theorems.Thm_ULHC_Adj_ends
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Adj_unit
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
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
theorem _root_.solution {u v : Pt} (h : Adj G u v) (B : Finset Edge) :
    ∃ tf : ℤ, ∑ e ∈ B, stepFlow u v e = (if ∃ e ∈ B, Ends e u v then 1 else 0) + 2 * tf := by
  obtain ⟨e0, _, h0⟩ := h.ends
  have hz : ∀ e, e ≠ e0 → stepFlow u v e = 0 := by
    intro e he
    by_contra hne
    exact he (Edge.eq_of_ends (stepFlow_ne_zero hne) h0)
  have huv : u ≠ v := by
    intro he; have := h.unit; rw [he] at this; simp [Unit] at this
  have hv : stepFlow u v e0 = 1 ∨ stepFlow u v e0 = -1 := by
    unfold stepFlow
    rcases h0 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      rw [if_pos ⟨a1, a2⟩, if_neg (fun h' => huv (a1.symm.trans h'.1))]; ring
    · right
      rw [if_neg (fun h' => huv (h'.1.symm.trans a1)), if_pos ⟨a1, a2⟩]; ring
  have hsum : ∑ e ∈ B, stepFlow u v e = if e0 ∈ B then stepFlow u v e0 else 0 := by
    rw [← Finset.sum_ite_eq' B e0 (fun e => stepFlow u v e)]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e = e0
    · simp [he]
    · simp [he, hz e he]
  have hex : (∃ e ∈ B, Ends e u v) ↔ e0 ∈ B := by
    constructor
    · rintro ⟨e, he, h1⟩; rwa [Edge.eq_of_ends h1 h0] at he
    · exact fun h => ⟨e0, h, h0⟩
  rw [hsum]
  by_cases hB : e0 ∈ B
  · rw [if_pos hB, if_pos (hex.2 hB)]
    rcases hv with hv | hv
    · exact ⟨0, by rw [hv]; ring⟩
    · exact ⟨-1, by rw [hv]; ring⟩
  · rw [if_neg hB, if_neg (fun h => hB (hex.1 h))]; exact ⟨0, by ring⟩
end ULHC
