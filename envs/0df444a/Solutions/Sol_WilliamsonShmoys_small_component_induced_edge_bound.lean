-- Prove2me | solution 1 for WilliamsonShmoys.small_component_induced_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:51:50.803966+00:00
-- url     : https://prove2.me/submissions/472c319f-f06d-455d-9326-c6fbd3ef6575

import Mathlib
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (C : K.ConnectedComponent)
    (hC : C.supp.ncard < 3) :
    (K.induce C.supp).edgeSet.ncard ≤ C.supp.ncard := by
  classical
  have hch : (K.induce C.supp).edgeSet.ncard ≤ (C.supp.ncard).choose 2 := by
    have h1 := (K.induce C.supp).card_edgeFinset_le_card_choose_two
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h1
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h1
  have hc2 : (C.supp.ncard).choose 2 ≤ C.supp.ncard := by
    interval_cases C.supp.ncard <;> decide
  omega
