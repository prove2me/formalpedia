-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:54:34.764235+00:00
-- url     : https://prove2.me/submissions/d85c9e37-f397-433f-a0cd-8e551f08a302
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hupper : L.edgeFinset.card <= 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
      L hL hcard
  have hlower : 3 * Fintype.card V - 6 <= L.edgeFinset.card :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
      L hL hcard hmax
  omega