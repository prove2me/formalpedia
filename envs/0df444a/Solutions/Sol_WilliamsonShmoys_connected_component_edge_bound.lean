-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:50:48.252851+00:00
-- url     : https://prove2.me/submissions/e4ebda81-a771-4470-9483-c4964de4974f

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (C : Set V) [Fintype C]
    (hC : C.Nonempty)
    (hconnected : (K.induce C).Connected)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    (K.induce C).edgeSet.ncard ≤
      (if C.ncard < 3 then C.ncard - 1 else 3 * C.ncard - 6) := by
  classical
  have hcard : Fintype.card C = C.ncard := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  split_ifs with h
  · have hs := SimpleGraph.card_edgeFinset_le_card_choose_two (G := K.induce C)
    have he : (K.induce C).edgeFinset.card = (K.induce C).edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [he, hcard] at hs
    have hpos : 0 < C.ncard := (Set.ncard_pos (Set.toFinite C)).mpr hC
    interval_cases h' : C.ncard
    · rw [show Nat.choose 1 2 = 0 from rfl] at hs; omega
    · rw [show Nat.choose 2 2 = 1 from rfl] at hs; omega
  · have := hconn C (by rw [hcard]; omega) hconnected
    rwa [hcard] at this
end WilliamsonShmoys

