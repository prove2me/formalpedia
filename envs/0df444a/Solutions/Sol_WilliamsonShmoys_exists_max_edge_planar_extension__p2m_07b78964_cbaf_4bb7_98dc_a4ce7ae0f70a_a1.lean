-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:01.616929+00:00
-- url     : https://prove2.me/submissions/660a776e-a6ef-421c-ba4d-7862d8f3d139

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
      M HasPlanarDrawingOn hM
  refine ⟨N, hMN, hN, ?_, hmax⟩
  exact hmax M le_rfl hM