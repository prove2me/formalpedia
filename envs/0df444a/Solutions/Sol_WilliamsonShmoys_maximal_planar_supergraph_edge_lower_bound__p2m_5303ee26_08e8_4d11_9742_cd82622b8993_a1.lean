-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:41.300572+00:00
-- url     : https://prove2.me/submissions/6f4e2e03-797c-4008-970a-2eaf80d18930

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ dN : DecidableRel N.Adj,
      (letI : DecidableRel N.Adj := dN
       3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  classical
  refine ⟨Classical.decRel _, ?_⟩
  letI : DecidableRel N.Adj := Classical.decRel _
  obtain ⟨f, heuler, htriangles⟩ :=
    WilliamsonShmoys.maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1
      N hN hcard hmax
  omega