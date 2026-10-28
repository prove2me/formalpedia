-- Prove2me | solution 1 for WilliamsonShmoys.connect_drawn_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:02:05.141983+00:00
-- url     : https://prove2.me/submissions/d8983226-652e-4030-ae30-9147cd2080c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_step
import Theorems.Thm_FiniteGraph_connected_supergraph_of_step

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected := by
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  have hstep :
      ∀ F : SimpleGraph V, G.edgeSet ⊆ F.edgeSet → P F → ¬ F.Connected →
        ∃ H : SimpleGraph V,
          F.edgeSet ⊆ H.edgeSet ∧ P H ∧
            ∃ u v : V, ¬ F.Reachable u v ∧ H.Reachable u v := by
    intro F hGF hPF hF
    exact WilliamsonShmoys.planar_edge_step F hPF hF
  exact FiniteGraph.connected_supergraph_of_step P G hDraw hstep