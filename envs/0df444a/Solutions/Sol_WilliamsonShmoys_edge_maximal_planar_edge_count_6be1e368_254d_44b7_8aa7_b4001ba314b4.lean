-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:36:55.102707+00:00
-- url     : https://prove2.me/submissions/f531c84d-67de-4c90-ab14-203eafccedb0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_same_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_same_vertices H hV hdraw
  have hKH : K = H := hmax K hsub hKdraw
  rw [hKH] at hcount
  exact hcount