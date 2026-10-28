-- Prove2me | solution 1 for WilliamsonShmoys.same_vertex_edge_maximal_planar_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:24:57.469087+00:00
-- url     : https://prove2.me/submissions/284fa87f-dc36-4dc9-9fbd-427ae91b7c61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_same_vertex_edge_bound_of_planar_drawing
import Theorems.Thm_WilliamsonShmoys_same_vertex_planar_extension_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall K : SimpleGraph V, G <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hLower⟩ :=
    WilliamsonShmoys.same_vertex_planar_extension_lower_bound G hV hG
  have hEq : K = G := hmax K hGK hK
  have hLowerG : 3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
    rw [← hEq]
    exact hLower
  have hUpper : G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.same_vertex_edge_bound_of_planar_drawing G hV hG
  exact le_antisymm hUpper hLowerG