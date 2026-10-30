-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:08:12.110499+00:00
-- url     : https://prove2.me/submissions/e59f168b-3109-4051-982d-5c38cd7d2798

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_completion_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_completion_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_for_completion_20261026 L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_edge_count_for_completion_20261026 M hM hV hmax⟩