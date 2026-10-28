-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:21:40.072383+00:00
-- url     : https://prove2.me/submissions/008e24b8-a48d-4e34-b8cd-b0f1e8c91c63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      Set.Subset M.edgeSet N.edgeSet →
      Set.Subset N.edgeSet M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hN, hMN, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61 M hM hV
  have hNM := hmax N hN hMN
  have hcard := WilliamsonShmoys.edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61 N M hNM
  omega