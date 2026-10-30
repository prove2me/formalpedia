-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:34:52.30693+00:00
-- url     : https://prove2.me/submissions/3c52e732-f24a-40f6-b081-cc650cd3a7d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H →
        Set.Subset K.edgeSet H.edgeSet →
        Set.Subset H.edgeSet K.edgeSet) := by
  obtain ⟨K, hK, hGK, hmax⟩ :=
    finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2
      (V := V) (G := G) WilliamsonShmoys.HasPlanarDrawingOn hG
  exact ⟨K, hGK, hK, hmax⟩