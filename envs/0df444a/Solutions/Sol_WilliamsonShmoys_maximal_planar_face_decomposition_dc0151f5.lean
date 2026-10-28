-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_dc0151f5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:37:13.663579+00:00
-- url     : https://prove2.me/submissions/0fdb1c5a-5db4-480f-9373-e1fbdecbedcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_retry_2cbac039
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_retry_2cbac039
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → M.edgeSet = L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_bound_retry_2cbac039 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039 L hL hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega