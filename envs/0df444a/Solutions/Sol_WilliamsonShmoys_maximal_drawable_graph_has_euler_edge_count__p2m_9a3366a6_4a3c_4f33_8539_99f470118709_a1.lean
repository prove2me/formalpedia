-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:11.038955+00:00
-- url     : https://prove2.me/submissions/4f4e7957-ce76-4dc6-b53d-2412f6bd9e7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M <= N → HasPlanarDrawingOn N → N = M) :
    M.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
      M dM hM hcard
  have hLower :=
    WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
      M dM hM hcard hmax
  omega