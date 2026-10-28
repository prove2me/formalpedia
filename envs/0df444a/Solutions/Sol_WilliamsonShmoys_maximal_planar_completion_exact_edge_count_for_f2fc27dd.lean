-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_exact_edge_count_for_f2fc27dd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:35:55.494344+00:00
-- url     : https://prove2.me/submissions/c7e17043-2c11-4baa-8cc5-0b5d16407e43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_for_f2fc27dd
import Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_for_f2fc27dd H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd K hV hK hmax⟩