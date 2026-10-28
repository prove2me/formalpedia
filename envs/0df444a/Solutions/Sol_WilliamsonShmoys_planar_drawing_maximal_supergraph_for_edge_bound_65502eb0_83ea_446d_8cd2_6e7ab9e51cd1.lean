-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:29:53.020106+00:00
-- url     : https://prove2.me/submissions/6d8d6095-042f-4eaf-be50-009c3e4c3f7f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hH, hKH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1 K hK
  refine ⟨H, hH, hKH, hmax, ?_⟩
  exact Set.ncard_mono hKH