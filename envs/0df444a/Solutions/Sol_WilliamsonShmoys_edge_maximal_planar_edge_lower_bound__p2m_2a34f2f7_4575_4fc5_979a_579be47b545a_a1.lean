-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_lower_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:08:30.893206+00:00
-- url     : https://prove2.me/submissions/5dbfd5bf-0b83-4f8f-bcc9-502e0533e549
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
      N hN hcard
  have hKN : K = N := hmax K hNK hK
  simpa [hKN] using hbound