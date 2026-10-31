-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:43.152046+00:00
-- url     : https://prove2.me/submissions/f989aa12-73a2-487c-a75c-d5bbc725d108

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V ≤ T.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee T hV hDraw hMax
