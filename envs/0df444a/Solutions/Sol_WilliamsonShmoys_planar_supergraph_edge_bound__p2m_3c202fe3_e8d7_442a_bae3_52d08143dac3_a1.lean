-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:38.939737+00:00
-- url     : https://prove2.me/submissions/e4f3b34f-f55f-405d-a2be-d795282200dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    exists T : SimpleGraph V,
      L <= T /\ HasPlanarDrawingOn T /\
        (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
          3 * Fintype.card V <= T.edgeFinset.card + 6) := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
      L hL
  refine ⟨T, hLT, hT, ?_⟩
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  exact WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
    T hT hmax hcard