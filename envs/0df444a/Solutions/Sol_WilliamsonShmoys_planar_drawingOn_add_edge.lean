-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_add_edge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:47:33.60737+00:00
-- url     : https://prove2.me/submissions/eee6585c-615b-44d5-a5ea-1ba1e57343ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_add_edge_geometry

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (u v : V)
    (huv : u ≠ v)
    (hnotReachable : ¬ P.Reachable u v) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ x y, P.Reachable x y → Q.Reachable x y) ∧
      Q.Reachable u v := by
  obtain ⟨Q, hPQ, hdrawQ, huvQ⟩ :=
    WilliamsonShmoys.planar_drawingOn_add_edge_geometry P hdraw u v huv hnotReachable
  refine ⟨Q, hPQ, hdrawQ, ?_, ?_⟩
  · intro x y hxy
    exact hxy.mono hPQ
  · exact huvQ.reachable