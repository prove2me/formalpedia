-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:07:53.069879+00:00
-- url     : https://prove2.me/submissions/56fd68e3-8e39-4e09-a0db-e0325cfcf618

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDrawH, hCount, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc K hK
  exact ⟨H, hKH, hDrawH, hCount,
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hV hDrawH hMax⟩