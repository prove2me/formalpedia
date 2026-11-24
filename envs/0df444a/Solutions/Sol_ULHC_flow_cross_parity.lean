-- Prove2me | solution 1 for ULHC.flow_cross_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:29:41.315683+00:00
-- url     : https://prove2.me/submissions/fe82c6bd-1342-4e54-883d-ccccc8a9e6eb

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_stepFlow_sum
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution (B : Finset Edge) {u : Pt} {l : List Pt}
    (hc : List.IsChain (Adj G) (u :: l)) :
    ∃ tf : ℤ, ∑ e ∈ B, flowL u l e = (crossL B u l : ℤ) + 2 * tf := by
  induction l generalizing u with
  | nil => exact ⟨0, by simp [flowL, crossL]⟩
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    obtain ⟨t1, h1⟩ := stepFlow_sum hc.1 B
    obtain ⟨t2, h2⟩ := ih hc.2
    refine ⟨t1 + t2, ?_⟩
    simp only [flowL, Finset.sum_add_distrib, crossL, h1, h2]
    push_cast
    split_ifs <;> ring
end ULHC
