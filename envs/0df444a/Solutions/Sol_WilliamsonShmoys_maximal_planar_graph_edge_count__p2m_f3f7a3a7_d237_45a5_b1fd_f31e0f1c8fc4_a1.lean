-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:52.682487+00:00
-- url     : https://prove2.me/submissions/49f2206c-7753-47e4-bb7a-4eee61520728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_upper_bound__p2m_b64ef977_b4ef_4b2b_beae_4cc23cd005bf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_b64ef977_b4ef_4b2b_beae_4cc23cd005bf_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn J)
    (hmax : ∀ L : SimpleGraph V,
      J.edgeSet ⊂ L.edgeSet → ¬ HasPlanarDrawingOn L) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b64ef977_b4ef_4b2b_beae_4cc23cd005bf_a1 J hcard hplanar
  have hl := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b64ef977_b4ef_4b2b_beae_4cc23cd005bf_a1 J hcard hplanar hmax
  omega