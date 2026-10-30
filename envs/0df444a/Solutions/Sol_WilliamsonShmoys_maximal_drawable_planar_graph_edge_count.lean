-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_graph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:14:22.444022+00:00
-- url     : https://prove2.me/submissions/598bb0f2-86e1-4281-bea0-2335c07901b3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_euler
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound_from_euler K hdraw hV
  obtain ⟨L, hKL, hLdraw, hLcount⟩ :=
    WilliamsonShmoys.drawable_triangulation_supergraph K hdraw hV
  have hmaxL := hmax L hKL hLdraw
  apply Nat.le_antisymm hupper
  calc
    3 * Fintype.card V - 6 = L.edgeSet.ncard := hLcount
    _ ≤ K.edgeSet.ncard := hmaxL