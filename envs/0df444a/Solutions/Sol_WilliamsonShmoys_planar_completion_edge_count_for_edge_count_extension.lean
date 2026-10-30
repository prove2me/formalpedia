-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_for_edge_count_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:01:51.305215+00:00
-- url     : https://prove2.me/submissions/844c1dfb-196b-4786-bb52-6612c10177ad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_by_edge_inclusion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_maximal_edge_count

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      HasPlanarDrawingOn K ∧
      J.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hK, hJK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_by_edge_inclusion J hJ
  exact ⟨K, hK, hJK,
    WilliamsonShmoys.maximal_planar_drawing_has_maximal_edge_count K hK hmax hV⟩