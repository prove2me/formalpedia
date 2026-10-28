-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:21:26.077021+00:00
-- url     : https://prove2.me/submissions/a91acc33-1841-4fb9-979e-b5b47a1b3672
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_0e98e963_983c_4fb9_9e38_7bdda2495dff_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_0e98e963_983c_4fb9_9e38_7bdda2495dff_a1 G hV hG