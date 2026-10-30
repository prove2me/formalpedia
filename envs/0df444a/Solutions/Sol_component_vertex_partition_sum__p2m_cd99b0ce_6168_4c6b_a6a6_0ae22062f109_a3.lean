-- Prove2me | solution 1 for component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:33.204448+00:00
-- url     : https://prove2.me/submissions/71bc504e-0f7c-49de-b4ef-248c48f44a1e

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Finprod

open SimpleGraph

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    Finset.univ.sum (fun C : G.ConnectedComponent => Nat.card (C : Set V)) =
      Fintype.card V := by
  classical
  simp only [Nat.card_coe_set_eq]
  calc
    (Finset.univ.sum fun C : G.ConnectedComponent => C.supp.ncard) =
        (⋃ C : G.ConnectedComponent, C.supp).ncard := by
      symm
      rw [Set.ncard_iUnion_of_finite
        (s := fun C : G.ConnectedComponent => C.supp)
        (hs := fun C => (Set.finite_univ : (Set.univ : Set V).Finite).subset
          (Set.subset_univ _))
        (h := SimpleGraph.pairwise_disjoint_supp_connectedComponent G)]
      exact finsum_eq_sum_of_fintype
        (fun C : G.ConnectedComponent => C.supp.ncard)
    _ = Fintype.card V := by
      rw [G.iUnion_connectedComponentSupp]
      simp