-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:31.443533+00:00
-- url     : https://prove2.me/submissions/0e0ab5ea-fc9b-4ed8-be21-8f1dfcfd196c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L)
    (hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    L = K := by
  classical
  have hsub : K.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_mono hKL
  have hfin : L.edgeSet.Finite := Set.toFinite _
  have := Set.eq_of_subset_of_ncard_le hsub hcard hfin
  exact (SimpleGraph.edgeSet_inj.mp this.symm)
