-- Prove2me | solution 1 for ULHC.handshake
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:44.502105+00:00
-- url     : https://prove2.me/submissions/39dc8294-4125-4a8e-8de1-345859190e79

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_sum_shift_eq
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
theorem _root_.solution {F : Finset Edge} {K : Finset Pt} (hK : Closed F K) :
    Even (∑ x ∈ K, deg F x) := by
  have e1 : ∀ x, deg F x = ind F (eR x) + ind F (eU x) + ind F (eL x) + ind F (eD x) := by
    intro x; unfold deg; ring
  simp only [e1, Finset.sum_add_distrib]
  have c : ∀ g : Pt → Edge, ∑ x ∈ K, ind F (g x) = (K.filter (fun x => g x ∈ F)).card := by
    intro g; unfold ind; simp [Finset.sum_boole]
  rw [c, c, c, c]
  have hL : (K.filter (fun x => eL x ∈ F)).card = (K.filter (fun x => eR x ∈ F)).card := by
    apply sum_shift_eq hK (fun x => (x.1 - 1, x.2)) (fun x => (x.1 + 1, x.2))
    · intro x; simp
    · intro x; simp
    · intro x; simp [eL, eR]
    · intro x hx; exact ⟨_, hx, Or.inr ⟨by simp [eL], by simp [eL, Edge.q]⟩⟩
    · intro x hx; exact ⟨_, hx, Or.inl ⟨by simp [eR], by simp [eR, Edge.q]⟩⟩
  have hD : (K.filter (fun x => eD x ∈ F)).card = (K.filter (fun x => eU x ∈ F)).card := by
    apply sum_shift_eq hK (fun x => (x.1, x.2 - 1)) (fun x => (x.1, x.2 + 1))
    · intro x; simp
    · intro x; simp
    · intro x; simp [eD, eU]
    · intro x hx; exact ⟨_, hx, Or.inr ⟨by simp [eD], by simp [eD, Edge.q]⟩⟩
    · intro x hx; exact ⟨_, hx, Or.inl ⟨by simp [eU], by simp [eU, Edge.q]⟩⟩
  rw [hL, hD]
  exact ⟨(K.filter (fun x => eR x ∈ F)).card + (K.filter (fun x => eU x ∈ F)).card, by ring⟩
end ULHC
