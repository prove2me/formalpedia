-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:29:12.578787+00:00
-- url     : https://prove2.me/submissions/df2d2565-5712-4239-8239-cb1d41fc42ca

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) : T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 T hV hDraw
