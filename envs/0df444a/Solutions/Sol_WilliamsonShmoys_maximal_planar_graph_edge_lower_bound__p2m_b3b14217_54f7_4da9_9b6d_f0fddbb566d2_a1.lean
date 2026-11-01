-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:29.391448+00:00
-- url     : https://prove2.me/submissions/23a0bb49-e698-4d7d-b6ae-1a76e23f91f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨P, hNP, hPdraw, hPcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2 N hV hN
  have hPN : ∀ u v, P.Adj u v → N.Adj u v := hmax P hNP hPdraw
  have hEq : N = P := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    exact ⟨hNP u v, hPN u v⟩
  rw [hEq]
  exact le_of_eq hPcount