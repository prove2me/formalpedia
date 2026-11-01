-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_exists_maximal_extension__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:05.808317+00:00
-- url     : https://prove2.me/submissions/1f0c75e2-1c02-4c3b-88c0-7fb32451caab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  have hmono : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G := by
    intro G K hGK hK
    rcases hK with ⟨p, arc, hp, hEdges, hCross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hAdj
      exact hEdges u v huv (hGK hAdj)
    · intro u v x y huv hxy hAdj hAdj' hne t ht s hs heq
      exact hCross u v x y huv hxy (hGK hAdj) (hGK hAdj') hne t ht s hs heq
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2
    P H hH hmono