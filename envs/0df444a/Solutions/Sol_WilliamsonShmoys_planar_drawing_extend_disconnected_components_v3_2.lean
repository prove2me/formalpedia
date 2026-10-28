-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_extend_disconnected_components_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:22:55.837788+00:00
-- url     : https://prove2.me/submissions/d63067e3-ceae-4174-b97b-cc7518f34580
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_components_fixed_vertices_card_ge_three

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) := by
  classical
  rcases hGdraw with ⟨p, arc, hp, hEdgeDrawing, hNoCrossing⟩
  obtain ⟨H, hSub, hAdj, hBridge, hExtendedArcs⟩ :=
    WilliamsonShmoys.planar_drawing_extend_components_fixed_vertices_card_ge_three
      G p arc hp hEdgeDrawing hNoCrossing hCard hGdisc
  rcases hExtendedArcs with ⟨arc', _hOldArcs, hEdgeDrawing', hNoCrossing'⟩
  have hDrawing' : HasPlanarDrawingOn H := ⟨p, arc', hp, hEdgeDrawing', hNoCrossing'⟩
  exact ⟨H, hSub, hDrawing', hAdj, hBridge⟩