-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:40:37.633063+00:00
-- url     : https://prove2.me/submissions/36a01158-bb84-449b-a2ea-02abe4c70079
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists_419a1fb2_144c_4e12_b921_930e8d46d3d3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hDrawM, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists_419a1fb2_144c_4e12_b921_930e8d46d3d3 L hL
  exact ⟨M, hLM, hDrawM,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3 M hDrawM hCard hMax⟩