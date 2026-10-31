-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_3e9e8d1d_850d_47bc_8fcb_8ba9a27c268e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:33:06.35242+00:00
-- url     : https://prove2.me/submissions/b42f4823-40d3-4a30-b7f9-ef6af15bc93c

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧ R.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_has_triangulation_completion Q hV hDraw
