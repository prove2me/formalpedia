-- Prove2me | solution 1 for ULHC.class_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:13.919293+00:00
-- url     : https://prove2.me/submissions/7e2872f1-fa07-463c-99f8-57ab9ea6ff8f

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_handshake


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hV : Inside V G) (x : Pt) (S : Finset Pt)
    (h : ∀ z ∈ cls V G x, deg G z = if z ∈ S then 1 else 2) :
    Even ((cls V G x ∩ S).card) := by
  have hs := handshake (closed_cls hV x)
  have e1 : ∑ z ∈ cls V G x, deg G z =
      ∑ z ∈ cls V G x, (2 - (if z ∈ S then 1 else 0)) := by
    apply Finset.sum_congr rfl; intro z hz; rw [h z hz]; split_ifs <;> rfl
  have e2 : ∑ z ∈ cls V G x, (2 - (if z ∈ S then 1 else 0)) + (cls V G x ∩ S).card =
      2 * (cls V G x).card := by
    have e3 : (cls V G x ∩ S).card = ∑ z ∈ cls V G x, (if z ∈ S then 1 else 0) := by
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter]
    rw [e3, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _; split_ifs <;> rfl
  rw [e1] at hs
  obtain ⟨r, hr⟩ := hs
  refine ⟨(cls V G x).card - r, ?_⟩
  omega
end ULHC
