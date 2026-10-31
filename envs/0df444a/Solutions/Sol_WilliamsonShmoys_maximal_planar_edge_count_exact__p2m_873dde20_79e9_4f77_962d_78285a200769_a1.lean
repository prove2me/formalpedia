-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:37.12399+00:00
-- url     : https://prove2.me/submissions/6a83db6f-1e53-4a8d-80e0-a3789dc12737

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V = T.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2 T hV hDraw hMax
