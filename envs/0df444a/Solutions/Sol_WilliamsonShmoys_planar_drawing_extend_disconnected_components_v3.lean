-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extend_disconnected_components_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:39:30.685976+00:00
-- url     : https://prove2.me/submissions/b8157398-60b0-4a3b-b60a-d3d643cd35a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_components_with_fixed_vertices

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
    WilliamsonShmoys.planar_drawing_extend_components_with_fixed_vertices
      G p arc hp hEdgeDrawing hNoCrossing hGdisc
  rcases hExtendedArcs with ⟨arc', hEdgeDrawing', hNoCrossing'⟩
  have hDrawing' : HasPlanarDrawingOn H := ⟨p, arc', hp, hEdgeDrawing', hNoCrossing'⟩
  exact ⟨H, hSub, hDrawing', hAdj, hBridge⟩