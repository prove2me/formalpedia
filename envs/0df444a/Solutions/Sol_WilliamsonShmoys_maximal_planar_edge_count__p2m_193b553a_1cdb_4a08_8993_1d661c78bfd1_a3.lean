-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:46.079087+00:00
-- url     : https://prove2.me/submissions/44367fa8-37b4-4d47-90c1-bb4c2476aa6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L.edgeFinset = K.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hup :=
    WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
      K dK hK hcard
  have hlo :=
    WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
      K dK hK hcard hmax
  omega