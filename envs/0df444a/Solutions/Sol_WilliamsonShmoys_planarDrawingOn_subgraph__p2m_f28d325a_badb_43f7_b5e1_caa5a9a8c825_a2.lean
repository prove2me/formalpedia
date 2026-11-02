-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:56.949381+00:00
-- url     : https://prove2.me/submissions/b6b2454f-42d3-4f81-a639-7f5e79834546

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V} (hAB : A ≤ B)
    (hB : WilliamsonShmoys.HasPlanarDrawingOn B) :
    WilliamsonShmoys.HasPlanarDrawingOn A := by
  rcases hB with ⟨p, arc, hp, hEdge, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hEdge u v huv (hAB hadj)
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs hEq
    exact hCross u v x y huv hxy (hAB hadjuv) (hAB hadjxy) hne t ht s hs hEq