-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_unreachable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:13:43.868991+00:00
-- url     : https://prove2.me/submissions/a85ba349-078a-4da9-b856-a7cacb32c46e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_not_reachable_vertices_ne
import Theorems.Thm_WilliamsonShmoys_planar_drawing_clean_arc_of_unreachable
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_from_clean_arc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  have huv : u ≠ v :=
    WilliamsonShmoys.not_reachable_vertices_ne G hUnreachable
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · rcases WilliamsonShmoys.planar_drawing_clean_arc_of_unreachable
        G hG huv' hUnreachable with
      ⟨p, arc, γ, hp, hEdges, hCross, hγContinuous, hγInjective,
        hγStart, hγEnd, hγAvoid, hγCross⟩
    exact WilliamsonShmoys.planar_drawing_add_edge_from_clean_arc
      G huv' hUnreachable p arc γ hp hEdges hCross hγContinuous
      hγInjective hγStart hγEnd hγAvoid hγCross
  · have hUnreachable' : ¬ G.Reachable v u := by
      intro hReach
      exact hUnreachable (SimpleGraph.Reachable.symm hReach)
    rcases WilliamsonShmoys.planar_drawing_clean_arc_of_unreachable
        G hG hvu' hUnreachable' with
      ⟨p, arc, γ, hp, hEdges, hCross, hγContinuous, hγInjective,
        hγStart, hγEnd, hγAvoid, hγCross⟩
    obtain ⟨H, hGH, hAdj, hDrawing⟩ :=
      WilliamsonShmoys.planar_drawing_add_edge_from_clean_arc
        G hvu' hUnreachable' p arc γ hp hEdges hCross hγContinuous
        hγInjective hγStart hγEnd hγAvoid hγCross
    exact ⟨H, hGH, hAdj.symm, hDrawing⟩