-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:46.675225+00:00
-- url     : https://prove2.me/submissions/6f171c32-2e5b-4eb9-af17-f25429727360
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨f, heuler, htriangles⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ac618f5b_f1ff_4053_9ae3_bb0fc54b8c70_a1
      H hH hMax hCard
  omega