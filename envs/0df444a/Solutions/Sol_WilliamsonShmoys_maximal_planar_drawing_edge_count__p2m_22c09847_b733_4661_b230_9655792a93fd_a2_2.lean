-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:34:26.207987+00:00
-- url     : https://prove2.me/submissions/705289c1-1f52-4fa8-92dd-9739ae97e60c

import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph H hH hV hMax
