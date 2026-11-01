-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_61543ccf_c10c_45ac_85dc_db241ebaf64e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:50.931255+00:00
-- url     : https://prove2.me/submissions/42fe70b6-8db9-4b42-845e-a02fe29f2d9e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
      G hG
  have hedge :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
      K hcard hK hmax
  exact ⟨K, hGK, hK, hedge⟩