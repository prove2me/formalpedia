-- Prove2me | solution 1 for WilliamsonShmoys.component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T14:23:14.721473+00:00
-- url     : https://prove2.me/submissions/446723c2-a9aa-431e-95c1-6340d140668b

import Mathlib

open scoped BigOperators

/-- The vertex sets of the connected components of a finite graph partition the vertex set. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [Fintype L.ConnectedComponent] :
    (Finset.univ.sum fun c : L.ConnectedComponent => (c.supp).ncard) = Fintype.card V := by
  classical
  have hpair : Pairwise fun c c' : L.ConnectedComponent => Disjoint c.supp c'.supp :=
    SimpleGraph.pairwise_disjoint_supp_connectedComponent L
  have hfin : ∀ c : L.ConnectedComponent, (c.supp).Finite := fun c => Set.toFinite _
  have h := Set.ncard_iUnion_of_finite (s := fun c : L.ConnectedComponent => c.supp) hfin hpair
  rw [SimpleGraph.iUnion_connectedComponentSupp L, Set.ncard_univ,
    Nat.card_eq_fintype_card] at h
  rw [h]
  exact (finsum_eq_sum_of_fintype (fun c : L.ConnectedComponent => (c.supp).ncard)).symm
