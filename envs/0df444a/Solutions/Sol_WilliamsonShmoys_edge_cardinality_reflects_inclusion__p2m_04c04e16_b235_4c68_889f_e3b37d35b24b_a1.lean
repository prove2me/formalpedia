-- Prove2me | solution 1 for WilliamsonShmoys.edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:44.455584+00:00
-- url     : https://prove2.me/submissions/2dcb6ad3-2f80-4a4f-ba73-e40b098c58be

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K L : SimpleGraph V)
    (hKL : ∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v)
    (hcount : K.edgeSet.ncard ≥ L.edgeSet.ncard) :
    ∀ u v, L.Adj u v → K.Adj u v := by
  classical
  have hEq : K.edgeSet = L.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hKL) hcount
  have hGraph : K = L := SimpleGraph.edgeSet_injective hEq
  intro u v huv
  rw [hGraph]
  exact huv