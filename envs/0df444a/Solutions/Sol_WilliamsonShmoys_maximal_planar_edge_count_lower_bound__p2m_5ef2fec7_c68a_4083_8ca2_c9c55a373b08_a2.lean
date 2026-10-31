-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:25:55.456881+00:00
-- url     : https://prove2.me/submissions/cd025d82-6fa5-4938-9224-49a265431757

import Theorems.Thm_WilliamsonShmoys_maximal_drawing_density_bound_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hmax : ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ W) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ W.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawing_density_bound_ws W hW hmax hV
