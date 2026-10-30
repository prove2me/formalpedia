-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:21.362132+00:00
-- url     : https://prove2.me/submissions/73a101bf-425e-4551-97a7-030b9b0fc91c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_predicate_supergraph_finite__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        Set.Subset K.edgeSet L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet = L.edgeSet := by
  exact WilliamsonShmoys.exists_maximal_predicate_supergraph_finite__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1
    WilliamsonShmoys.HasPlanarDrawingOn
    (fun {A B} hAB hB =>
      WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset__p2m_90cbbd5c_48b8_4938_99ca_cd8db48989ee_a1 hAB hB)
    G hG