-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:34:07.035796+00:00
-- url     : https://prove2.me/submissions/c5c699cf-ca7a-4568-8707-3928d157b60b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_completion_maximal_extension_6e15fe35
import Theorems.Thm_WilliamsonShmoys_triangulation_completion_face_count_6e15fe35

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, G ≤ M ∧
      HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hGM, hM, hMax⟩ :=
    WilliamsonShmoys.triangulation_completion_maximal_extension_6e15fe35 G hG
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.triangulation_completion_face_count_6e15fe35 M hM hMax hCard
  refine ⟨M, hGM, hM, ?_⟩
  omega