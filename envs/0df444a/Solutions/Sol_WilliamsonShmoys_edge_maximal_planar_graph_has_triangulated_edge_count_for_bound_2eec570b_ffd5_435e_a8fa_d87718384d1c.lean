-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:44:17.831558+00:00
-- url     : https://prove2.me/submissions/e139d67e-6367-4a6c-9855-d2918cad75b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.edge_maximal_planar_edge_count_upper_bound H hH hCard
  have hLower := WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound H hH hMax hCard
  omega