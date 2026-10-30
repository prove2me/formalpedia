-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:08:05.282881+00:00
-- url     : https://prove2.me/submissions/4dda0719-7976-4487-935c-d43678617134

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_cardinality_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_max_cardinality_planar_supergraph N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_supergraph_has_triangulation_edge_count
      N hN hV K hNK hK hmax⟩