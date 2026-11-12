-- Prove2me | solution 1 for WilliamsonShmoys.componentwise_edge_bound_aggregate_component_local_bound__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T12:06:39.734638+00:00
-- url     : https://prove2.me/submissions/c7d63570-0e80-45aa-9c21-9327451149f1

import Mathlib

set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hlocal : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard ≤ 3 * S.card - 6)
    (c : K.ConnectedComponent) (hc : 3 ≤ c.supp.ncard) :
    (K.induce c.supp).edgeSet.ncard ≤ 3 * c.supp.ncard - 6 := by
  classical
  have hfin : c.supp.Finite := Set.toFinite _
  obtain ⟨S, hS⟩ : ∃ S : Finset V, (↑S : Set V) = c.supp :=
    ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hScard : S.card = c.supp.ncard := by
    rw [← Set.ncard_coe_finset S, hS]
  have hconn : (K.induce (↑S : Set V)).Connected := by
    rw [hS]
    exact c.connected_toSimpleGraph
  have h3 : 3 ≤ S.card := by omega
  have h := hlocal S h3 hconn
  rw [hS] at h
  rw [← hScard]
  exact h
