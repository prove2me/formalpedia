-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_supergraph_same_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:47:03.575309+00:00
-- url     : https://prove2.me/submissions/3b01a808-ce2a-49c4-9ce3-5299b4c4e842
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_same_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_triangulated_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      X ≤ H ∧
      (X.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hH, hXH, hMono, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertices X hX hCard
  have hCount := WilliamsonShmoys.maximal_drawing_has_triangulated_edge_count H hH hCard hMax
  exact ⟨H, hH, hXH, hMono, hCount⟩