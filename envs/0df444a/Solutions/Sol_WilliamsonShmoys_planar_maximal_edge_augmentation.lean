-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:48:17.858168+00:00
-- url     : https://prove2.me/submissions/60c47976-2419-4725-aeda-20ec547d7f02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_fixed_vertex_set
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_fixed_vertex_set

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists_fixed_vertex_set L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count_fixed_vertex_set
      M hM hmax hV⟩