-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:13:40.97797+00:00
-- url     : https://prove2.me/submissions/81b05db5-4793-4751-b0eb-c6f48bc63fa4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    Exists fun K : SimpleGraph V =>
      H <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 /\
      H.edgeSet.ncard <= K.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hKconn, hedge, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_finite_v2 H hH hconn
  have hcount := WilliamsonShmoys.maximal_planar_drawing_edge_count_v2
    K hV hK hKconn hmax
  exact ⟨K, hHK, hK, hcount, hedge⟩