-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T15:55:41.751702+00:00
-- url     : https://prove2.me/submissions/ccac12d7-9b62-46a3-89f0-ef957619f4fb

import Mathlib

/-- A connected component supported on at most two vertices spans at most one edge. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (c : L.ConnectedComponent) (hsmall : c.supp.ncard ≤ 2) :
    (L.induce c.supp).edgeSet.ncard ≤ 1 := by
  classical
  have hcard : Fintype.card c.supp ≤ 2 := by
    have h' : c.supp.toFinset.card ≤ 2 := by
      rwa [Set.ncard_eq_toFinset_card'] at hsmall
    rwa [Set.toFinset_card] at h'
  have h1 : (L.induce c.supp).edgeFinset.card ≤ (Fintype.card c.supp).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have h2 : (L.induce c.supp).edgeSet.ncard = (L.induce c.supp).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  rw [h2]
  have hchoose : (Fintype.card c.supp).choose 2 ≤ 1 := by
    rcases le_or_gt (Fintype.card c.supp) 1 with h | h
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      omega
    · have h2 : Fintype.card c.supp = 2 := by omega
      rw [h2]
      norm_num
  omega
