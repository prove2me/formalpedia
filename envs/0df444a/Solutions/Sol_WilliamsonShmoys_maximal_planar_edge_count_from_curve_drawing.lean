-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:34:43.045822+00:00
-- url     : https://prove2.me/submissions/65a13b98-1895-4d51-8968-ee4ef8d5c2b8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨N, hMN, hN, hCard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex
      M hV hM
  have hEq : N = M := hMax N hMN hN
  rw [hEq] at hCard
  omega