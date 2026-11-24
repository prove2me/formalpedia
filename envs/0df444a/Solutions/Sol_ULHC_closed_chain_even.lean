-- Prove2me | solution 1 for ULHC.closed_chain_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:31:53.194106+00:00
-- url     : https://prove2.me/submissions/eb22d676-1785-4c52-b5d6-fef05bb73e56

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_pot_zero_off_cells
import Theorems.Thm_ULHC_sum_hi_lo
import Theorems.Thm_ULHC_flowL_mem
import Theorems.Thm_ULHC_flow_cross_parity
import Theorems.Thm_ULHC_Adj_unit
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_outflow_flowL
import Theorems.Thm_ULHC_pot_jump
import Theorems.Thm_ULHC_rot_balanced
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
theorem _root_.solution {V : Finset Pt} (hs : Solid V) (hG : ∀ e ∈ G, e.p ∈ V ∧ e.q ∈ V)
    (B : Finset Edge) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
    {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l))
    (hl : (u :: l).getLast (by simp) = u) : crossL B u l % 2 = 0 := by
  set f := flowL u l
  have hunit : List.IsChain Unit (u :: l) := hc.imp (fun _ _ h => h.unit)
  have hout : ∀ x, outflow f x = 0 := by
    intro x; rw [outflow_flowL u l hunit x, hl]; ring
  have hS : Supp G (rot f) := by
    intro e he
    have : f e = 0 := by by_contra h; exact he (flowL_mem hc h)
    unfold rot; cases e.d <;> simp [this]
  have hb := rot_balanced hout
  set W := pot G (rot f)
  have hj : ∀ e, W e.hi - W e.lo = rot f e := pot_jump hS hb
  have hz : ∀ c, ¬ IsCell V c → W c = 0 := fun c hc' => pot_zero_off_cells hS hb hG hs hc'
  -- `Σ_B (W hi + W lo)` is even.
  set T := B.image Edge.hi ∪ B.image Edge.lo
  have hT : ∀ e ∈ B, e.hi ∈ T ∧ e.lo ∈ T := fun e he =>
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ he),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)⟩
  have hev : Even (∑ e ∈ B, (W e.hi + W e.lo)) := by
    rw [sum_hi_lo B W T hT]
    apply Finset.even_sum
    intro c _
    by_cases hcell : IsCell V c
    · have := heven c hcell
      obtain ⟨r, hr⟩ : ∃ r, sidesIn B c = 2 * r := ⟨sidesIn B c / 2, by omega⟩
      rw [hr]; push_cast; exact ⟨W c * r, by ring⟩
    · rw [hz c hcell]; simp
  -- Hence `Σ_B rot f` and `Σ_B f` are even.
  have hrot : Even (∑ e ∈ B, rot f e) := by
    have e1 : ∑ e ∈ B, rot f e = ∑ e ∈ B, (W e.hi + W e.lo) - 2 * ∑ e ∈ B, W e.lo := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro e _; rw [← hj]; ring
    rw [e1]; obtain ⟨r, hr⟩ := hev; exact ⟨r - ∑ e ∈ B, W e.lo, by rw [hr]; ring⟩
  have hf : Even (∑ e ∈ B, f e) := by
    have e2 : ∑ e ∈ B, f e = ∑ e ∈ B, rot f e + 2 * ∑ e ∈ B.filter (fun e => e.d = .v), f e := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro e _
      unfold rot; cases e.d <;> simp; ring
    rw [e2]; obtain ⟨r, hr⟩ := hrot; exact ⟨r + ∑ e ∈ B.filter (fun e => e.d = .v), f e, by rw [hr]; ring⟩
  obtain ⟨tf, ht⟩ := flow_cross_parity B hc
  obtain ⟨r, hr⟩ := hf
  have : (crossL B u l : ℤ) = 2 * (r - tf) := by rw [hr] at ht; linarith
  omega
end ULHC
