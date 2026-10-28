-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:43:24.769114+00:00
-- url     : https://prove2.me/submissions/845dff07-13a7-492a-a3c8-c59b04bc5a0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDrawing : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDrawing, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
      L hDrawing
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605
      M hMDrawing hCard hMaximal
  exact ⟨M, hLM, hMDrawing, hEdges⟩