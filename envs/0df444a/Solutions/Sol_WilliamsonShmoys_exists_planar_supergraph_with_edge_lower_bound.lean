-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:20:54.861988+00:00
-- url     : https://prove2.me/submissions/c2af857e-34cf-45d8-9430-cf5a9aaa2c4f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_1b538d07
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_1b538d07

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_1b538d07 J hJ
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.maximal_planar_edge_lower_bound_1b538d07 K hV hK hmax⟩