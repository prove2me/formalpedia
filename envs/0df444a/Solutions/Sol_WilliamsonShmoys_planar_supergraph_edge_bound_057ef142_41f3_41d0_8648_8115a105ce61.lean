-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:03:17.336853+00:00
-- url     : https://prove2.me/submissions/0a864843-178f-4a83-8ec2-5e68f2e8254b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn N)
        (And (Set.Subset M.edgeSet N.edgeSet)
          (3 * Fintype.card V <= N.edgeSet.ncard + 6)) := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension_3624186a_b460_4cf9_8afd_86ec1a2d5ee8 M hM
  exact ⟨N, hN, hMN,
    WilliamsonShmoys.maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8 N hN hmax hV⟩