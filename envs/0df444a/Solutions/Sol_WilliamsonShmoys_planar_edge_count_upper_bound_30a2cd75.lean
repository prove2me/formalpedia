-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_30a2cd75
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:00:09.862336+00:00
-- url     : https://prove2.me/submissions/8d4b5b41-c1bc-4304-8dd9-24cc191df761
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hcount, hH, hconn⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
      M hM hV
  exact hcount.trans
    (WilliamsonShmoys.connected_planar_edge_bound_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
      H hH hconn hV)