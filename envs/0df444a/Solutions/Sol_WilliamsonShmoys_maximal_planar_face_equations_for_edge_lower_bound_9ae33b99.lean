-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations_for_edge_lower_bound_9ae33b99
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:53:32.020437+00:00
-- url     : https://prove2.me/submissions/2ffc081b-b2bf-4a97-b8cf-079f42d42651
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices
import Theorems.Thm_WilliamsonShmoys_planar_graph_below_edge_bound_can_be_augmented

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices L hL hCard
  have hnot : ¬ L.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hSmall
    obtain ⟨M, hsub, hPlanar, hNe⟩ :=
      WilliamsonShmoys.planar_graph_below_edge_bound_can_be_augmented L hL hCard hSmall
    exact hNe (hMax M hsub hPlanar)
  have hEq : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega