-- Prove2me | solution 1 for WilliamsonShmoys.planar_spanning_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:57:44.697463+00:00
-- url     : https://prove2.me/submissions/4d8ddc50-1359-406d-8a0e-789b2e554a24

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet ⊆ K'.edgeSet ∧
      K'.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K', hK', hsub, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5 K hK
  exact ⟨K', hK', hsub,
    WilliamsonShmoys.maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5 K' hV hK' hmax⟩