-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:01:27.446545+00:00
-- url     : https://prove2.me/submissions/abf19ef6-3523-404a-84db-8853605051cf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_face_equations_9ae33b99
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
import Mathlib.Tactic

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
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_bound_face_equations_9ae33b99
    L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
    L hL hMax hCard
  have hEdges : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
