-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_7607aed3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:19:12.935933+00:00
-- url     : https://prove2.me/submissions/2e0da846-99e8-4aea-afb4-625a73cad5a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_7607aed3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_7607aed3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hHK, hKdraw, hKconn, hKmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension_7607aed3 H hdraw hconn
  refine ⟨K, hHK, hKdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_7607aed3
    K hKconn hKdraw hKmax hV