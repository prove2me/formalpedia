-- Prove2me | solution 1 for ULHC.conn_erase_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:56.358887+00:00
-- url     : https://prove2.me/submissions/18fcbe8d-874c-4e30-a38d-9c46d714d7fe

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_handshake
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_symm
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {e : Edge}
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F e.p z → Even (deg F z)) :
    Conn (F.erase e) e.p e.q := by
  by_contra hn
  have hV' : Inside V (F.erase e) := hV.mono (Finset.erase_subset _ _)
  set K := cls V (F.erase e) e.p
  have hs := handshake (closed_cls hV' e.p)
  have hp : e.p ∈ K := mem_cls_self (hV e he).1
  have hq : e.q ∉ K := by
    unfold K cls; simp only [Finset.mem_filter, not_and]; exact fun _ h => hn h
  have hsum : ∑ x ∈ K, deg F x =
      ∑ x ∈ K, deg (F.erase e) x + ∑ x ∈ K, (if e.p = x ∨ e.q = x then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _; exact (deg_erase he x).symm
  have hone : ∑ x ∈ K, (if e.p = x ∨ e.q = x then 1 else 0) = 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
      mul_one]
    rw [Finset.card_eq_one]
    refine ⟨e.p, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact h.symm
      · subst h; exact absurd hx hq
    · rintro rfl; exact ⟨hp, Or.inl rfl⟩
  have hev : Even (∑ x ∈ K, deg F x) := by
    apply Finset.even_sum
    intro x hx
    unfold K cls at hx
    simp only [Finset.mem_filter] at hx
    exact heven x hx.1 (hx.2.mono (Finset.erase_subset _ _))
  rw [hsum, hone] at hev
  rw [Nat.even_add_one] at hev
  exact hev hs
end ULHC
