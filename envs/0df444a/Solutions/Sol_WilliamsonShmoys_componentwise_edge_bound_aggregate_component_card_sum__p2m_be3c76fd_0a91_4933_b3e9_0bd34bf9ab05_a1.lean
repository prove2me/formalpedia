-- Prove2me | solution 1 for WilliamsonShmoys.componentwise_edge_bound_aggregate_component_card_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T15:34:19.020335+00:00
-- url     : https://prove2.me/submissions/5347271b-2340-4915-8fb8-39a729f617ce

import Mathlib

open scoped BigOperators

/-- The vertex sets of the connected components of a finite graph partition the vertex set. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    (∑ c : K.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
  classical
  have hpair : Pairwise fun c c' : K.ConnectedComponent => Disjoint c.supp c'.supp :=
    SimpleGraph.pairwise_disjoint_supp_connectedComponent K
  have hfin : ∀ c : K.ConnectedComponent, (c.supp).Finite := fun c => Set.toFinite _
  have h := Set.ncard_iUnion_of_finite (s := fun c : K.ConnectedComponent => c.supp) hfin hpair
  rw [SimpleGraph.iUnion_connectedComponentSupp K, Set.ncard_univ,
    Nat.card_eq_fintype_card] at h
  rw [h]
  exact (finsum_eq_sum_of_fintype (fun c : K.ConnectedComponent => (c.supp).ncard)).symm
