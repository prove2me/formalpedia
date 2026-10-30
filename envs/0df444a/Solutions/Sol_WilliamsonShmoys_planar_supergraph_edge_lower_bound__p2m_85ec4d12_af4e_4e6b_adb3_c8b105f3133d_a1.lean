-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:30.55328+00:00
-- url     : https://prove2.me/submissions/c80ff8dc-9538-4526-8f5b-c801ca66ab29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ [DecidableRel K.Adj],
        3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
      G hG
  refine ⟨K, hGK, hK, ?_⟩
  intro instK
  letI : DecidableRel K.Adj := instK
  have hmaxK : ∀ H : SimpleGraph V,
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K := by
    intro H hKH hH
    exact hmax H (le_trans hGK hKH) hH hKH
  exact WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
    K hK hmaxK hcard