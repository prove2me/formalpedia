-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:22:16.981628+00:00
-- url     : https://prove2.me/submissions/4e9b8822-c770-4377-9f70-4623ce19438f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset L.edgeSet M.edgeSet ->
      L.edgeSet = M.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hM, hsub, hbound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155 L hL hV
  have heq : L.edgeSet = M.edgeSet := hmax M hM hsub
  rw [← heq] at hbound
  exact hbound