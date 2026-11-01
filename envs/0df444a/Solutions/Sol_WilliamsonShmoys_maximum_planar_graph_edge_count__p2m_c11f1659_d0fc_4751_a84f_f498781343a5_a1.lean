-- Prove2me | solution 1 for WilliamsonShmoys.maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:59.263406+00:00
-- url     : https://prove2.me/submissions/ddf1e67b-199c-4c8c-be3c-1288b79ae0c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
import Theorems.Thm_WilliamsonShmoys_exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset.card ≥ L.edgeFinset.card) :
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨L, dL, hL, hLcount⟩ :=
    WilliamsonShmoys.exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2 hcard
  have hmaxL := hmax L dL hL
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
      K dK hcard hK
  omega