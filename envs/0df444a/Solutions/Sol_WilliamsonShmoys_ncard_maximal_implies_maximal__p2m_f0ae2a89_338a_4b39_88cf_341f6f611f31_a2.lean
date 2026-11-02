-- Prove2me | solution 1 for WilliamsonShmoys.ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:46.363208+00:00
-- url     : https://prove2.me/submissions/f250ebc8-edc6-433f-ac97-3b4311c2f931

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  intro M hLM hPlanar
  apply (SimpleGraph.edgeSetEmbedding V).injective
  change M.edgeSet = L.edgeSet
  exact (Set.eq_of_subset_of_ncard_le
    ((SimpleGraph.edgeSetEmbedding V).monotone hLM)
    (hmax M hLM hPlanar)).symm