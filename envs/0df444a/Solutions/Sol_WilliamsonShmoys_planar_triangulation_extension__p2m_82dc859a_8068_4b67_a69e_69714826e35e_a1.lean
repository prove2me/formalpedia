-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_82dc859a_8068_4b67_a69e_69714826e35e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:59.137922+00:00
-- url     : https://prove2.me/submissions/fdf5e232-3bb3-4b05-a6f5-3f938cd2261d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
import Theorems.Thm_WilliamsonShmoys_simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2 H hV
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2 H hH hconn hV