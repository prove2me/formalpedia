-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_lower_of_maximal_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:31:32.827602+00:00
-- url     : https://prove2.me/submissions/a41108bb-ee90-43f4-a6c2-8674df6e08a1

import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge H hCard hH hmax
