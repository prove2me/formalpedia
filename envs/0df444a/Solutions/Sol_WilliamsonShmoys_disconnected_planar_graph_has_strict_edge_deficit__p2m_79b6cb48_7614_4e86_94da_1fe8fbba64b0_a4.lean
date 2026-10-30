-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:18.381403+00:00
-- url     : https://prove2.me/submissions/881d7f26-66a9-44fc-a564-04e50cebfc43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    H.edgeSet.ncard + 6 < 3 * Fintype.card V := by
  obtain ⟨H', hplanar', hconnected', hmore⟩ :=
    WilliamsonShmoys.disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
      H hplanar hV hdisconnected
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
      H' hplanar' hconnected' hV
  omega