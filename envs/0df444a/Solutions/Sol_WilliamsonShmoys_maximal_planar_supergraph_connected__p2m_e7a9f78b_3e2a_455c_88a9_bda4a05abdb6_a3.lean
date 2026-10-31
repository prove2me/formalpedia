-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:59.64354+00:00
-- url     : https://prove2.me/submissions/91b2a837-ccdb-41c4-8b82-d540e8a61790
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L) :
    L.Connected := by
  by_contra hNotConnected
  obtain ⟨N, hSub, hPlanar, hNotSub⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1
      L hL hV hNotConnected
  exact hNotSub (hMax N hSub hPlanar)