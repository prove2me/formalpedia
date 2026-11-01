-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:36.236304+00:00
-- url     : https://prove2.me/submissions/bcb1c308-6c6e-497a-a3e6-4930aad5c96b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKconn, hKdraw, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
      H hH hcard
  have hConnectedBound :=
    WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
      K hKdraw hKconn hcard
  exact le_trans hEdges hConnectedBound