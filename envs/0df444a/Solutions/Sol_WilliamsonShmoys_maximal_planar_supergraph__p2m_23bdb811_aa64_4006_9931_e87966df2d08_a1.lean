-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:52:02.094644+00:00
-- url     : https://prove2.me/submissions/2f7a6028-e21c-4350-8d8e-9fb4728f5655
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
      K hK
  obtain hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
      L hL hV hMax
  refine ⟨L, hKL, hL, ?_⟩
  omega