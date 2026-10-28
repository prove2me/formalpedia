-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:44:31.227449+00:00
-- url     : https://prove2.me/submissions/be16f6cd-6298-43fc-9a56-9837452a2cc0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRconn : R.Connected)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hRH, hHdraw, hHmax, hcard⟩ :=
    WilliamsonShmoys_maximal_planar_extension_same_vertices R hV hRconn hR
  have hbound := WilliamsonShmoys_maximal_planar_edge_bound H hV hHdraw hHmax
  exact le_trans hcard hbound