-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_for_triangular_incidence_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:32:29.719273+00:00
-- url     : https://prove2.me/submissions/cb648dfe-f302-4ff5-83f9-0364600ecab9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_same_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    (X.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hXH, hSub, hEdges, hBound⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_supergraph_same_vertices
      X hX hCard
  rw [hBound] at hEdges
  exact hEdges