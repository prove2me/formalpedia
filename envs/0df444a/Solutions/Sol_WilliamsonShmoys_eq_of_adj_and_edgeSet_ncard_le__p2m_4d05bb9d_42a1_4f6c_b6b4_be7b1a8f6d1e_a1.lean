-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:36.266316+00:00
-- url     : https://prove2.me/submissions/fa16d2a4-8624-4f43-8e90-a21ea18d9298

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hsub : ∀ u v, H.Adj u v → K.Adj u v)
    (hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    K = H := by
  classical
  have hle : H ≤ K := by
    intro u v huv
    exact hsub u v huv
  have hHK : H.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_mono hle
  have hEdges : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le hHK hcard (Set.toFinite K.edgeSet)
  exact SimpleGraph.edgeSet_injective (hEdges.symm)