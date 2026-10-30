-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:07:37.22497+00:00
-- url     : https://prove2.me/submissions/59d26f7a-0c55-46da-839a-17f5ebd8ef2f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_maximal_edge_count
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_edge_count_monotone

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (n : Nat)
    (hLarge : 3 <= n)
    (hcard : Fintype.card V = n) :
    Exists fun K : SimpleGraph V =>
      G <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      G.edgeSet.ncard <= K.edgeSet.ncard /\
      K.edgeSet.ncard = 3 * n - 6 := by
  obtain ⟨K, hGK, hKDrawing, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_completion_exists_maximal_extension G hDrawing
  have hEdges :=
    WilliamsonShmoys.planar_drawing_triangulated_completion_edge_count_monotone G K hGK
  have hCount :=
    WilliamsonShmoys.planar_drawing_triangulated_completion_maximal_edge_count K hKDrawing
      hMaximal n hLarge hcard
  exact ⟨K, hGK, hKDrawing, hEdges, hCount⟩