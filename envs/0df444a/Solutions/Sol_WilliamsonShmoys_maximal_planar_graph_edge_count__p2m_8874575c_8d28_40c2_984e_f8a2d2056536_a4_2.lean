-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:50:09.439885+00:00
-- url     : https://prove2.me/submissions/3a9d281a-e57f-4a0b-b42e-460b02a12e21

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_136dc8a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : T.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_136dc8a1 T hV hDraw hMax
