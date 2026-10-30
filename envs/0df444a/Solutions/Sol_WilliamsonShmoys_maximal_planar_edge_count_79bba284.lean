-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_79bba284
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:34:30.608712+00:00
-- url     : https://prove2.me/submissions/5f691a60-0039-4ef9-9d04-4ea8e9b1f300

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099 L hV hL
  have hML : Set.Subset M.edgeSet L.edgeSet := hMax M hLM hM
  have hEdges : M.edgeSet = L.edgeSet := Set.Subset.antisymm hML hLM
  rw [hEdges] at hCount
  exact hCount