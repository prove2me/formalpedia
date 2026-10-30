-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_graph_has_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:29:45.690018+00:00
-- url     : https://prove2.me/submissions/7a29831d-83aa-4f70-ba36-77eb83de7fef

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_maximal_drawable_target
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_for_triangulation_target

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L → L ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_target M hM hCard
  have hLower : 3 * Fintype.card V - 6 ≤ M.edgeSet.ncard :=
    WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_for_triangulation_target M hM hmax hCard
  omega