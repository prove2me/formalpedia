-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:46.561062+00:00
-- url     : https://prove2.me/submissions/61248c8b-09ef-4973-a157-7fe5f4044303

import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_triangulated_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧ HasPlanarDrawingOn R ∧ R.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.drawable_supergraph_with_triangulated_edge_count Q hDraw hV
