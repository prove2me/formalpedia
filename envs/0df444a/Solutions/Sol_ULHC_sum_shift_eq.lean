-- Prove2me | solution 1 for ULHC.sum_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:15.684081+00:00
-- url     : https://prove2.me/submissions/7f9adcdc-dde0-406a-9046-4135629a3ce6

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
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
namespace ULHC
theorem _root_.solution {F : Finset Edge} {K : Finset Pt} (hK : Closed F K)
    (s : Pt → Pt) (tf : Pt → Pt) (hst : ∀ x, tf (s x) = x) (hts : ∀ x, s (tf x) = x)
    (g g' : Pt → Edge) (hg : ∀ x, g' (s x) = g x)
    (hadj : ∀ x, g x ∈ F → Adj F x (s x)) (hadj' : ∀ x, g' x ∈ F → Adj F x (tf x)) :
    ((K.filter (fun x => g x ∈ F)).card) = ((K.filter (fun x => g' x ∈ F)).card) := by
  apply Finset.card_bij' (fun x _ => s x) (fun x _ => tf x)
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hK x hx.1 _ (hadj x hx.2), by rw [hg]; exact hx.2⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨hK x hx.1 _ (hadj' x hx.2), ?_⟩
    rw [← hg, hts]; exact hx.2
  · intro x _; exact hst x
  · intro x _; exact hts x
end ULHC
