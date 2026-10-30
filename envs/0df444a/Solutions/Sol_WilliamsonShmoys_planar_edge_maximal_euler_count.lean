-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_euler_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:05:57.41999+00:00
-- url     : https://prove2.me/submissions/5fc6bc39-cef9-49ff-9e84-3d7c136628ec

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count_lower_bound
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_maximal_euler_count_upper_bound M hM hV
  have hlo := WilliamsonShmoys.planar_edge_maximal_euler_count_lower_bound M hM hmax hV
  omega