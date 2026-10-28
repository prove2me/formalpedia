-- Prove2me | solution 1 for WilliamsonShmoys.ceaeb6d3_maximal_planar_drawing_face_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:20:28.03199+00:00
-- url     : https://prove2.me/submissions/13f8d1b7-43e5-45c0-ad89-3cf79cbf9483
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_face_equations
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_face_equations

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      And (Fintype.card V + f = L.edgeSet.ncard + 2)
          (3 * f = 2 * L.edgeSet.ncard) := by
  have hUpper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_equations L hL hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_face_equations
      L hL hMax hCard
  have hEdges : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  constructor <;> omega