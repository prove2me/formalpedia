-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:51:27.155951+00:00
-- url     : https://prove2.me/submissions/688206e8-18f1-4a53-8c79-412e86b47b4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1 K hV hK
  have hlower := WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1 K hV hK hmax
  omega