-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:43.265078+00:00
-- url     : https://prove2.me/submissions/8f533725-6ba4-4b5d-aa64-740252640984

import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V - 6 ≤ T.edgeSet.ncard :=
  WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge T hV hT hmax
