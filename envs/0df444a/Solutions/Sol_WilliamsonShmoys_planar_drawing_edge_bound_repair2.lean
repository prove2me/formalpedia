-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_repair2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:23:13.486327+00:00
-- url     : https://prove2.me/submissions/11153aad-6146-4e58-b7fd-f7b3d303e667

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hKdraw, hKmax, hEdge⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2 G hG
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2 K hKdraw hKmax hV
  have hKcount : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  omega