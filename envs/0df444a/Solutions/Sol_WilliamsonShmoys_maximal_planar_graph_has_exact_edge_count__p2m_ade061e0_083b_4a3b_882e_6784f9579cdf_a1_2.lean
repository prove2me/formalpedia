-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:18:21.054141+00:00
-- url     : https://prove2.me/submissions/fde9f0d9-864c-42a6-9b37-d52b5bc4dc45

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2 K hK hmax hV
