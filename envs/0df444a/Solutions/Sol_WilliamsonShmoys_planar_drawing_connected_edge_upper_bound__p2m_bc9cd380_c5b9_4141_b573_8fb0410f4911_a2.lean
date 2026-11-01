-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:32.679471+00:00
-- url     : https://prove2.me/submissions/565faa83-091e-428a-9af7-db4a696f6c6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
import Theorems.Thm_WilliamsonShmoys_planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) <= 3 * Fintype.card V - 6 := by
  obtain ⟨k, faces, hlen, hcount, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2 G dG hG hConn hcard
  exact WilliamsonShmoys.planar_facial_walk_data_edge_bound__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
    G dG k faces hlen hcount heuler hcard