-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:54:35.995088+00:00
-- url     : https://prove2.me/submissions/5b2c76cc-6414-46ae-a703-c7b65e05936f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_edge_count_completion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal_for_edge_count_completion H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_for_completion K hK hmax hV⟩