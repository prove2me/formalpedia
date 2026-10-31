-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:10.829885+00:00
-- url     : https://prove2.me/submissions/8f34a07e-7b82-4d78-b95d-1dfba8aaffcc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = N.edgeSet) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
    N hV hN
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
    N hV hN hmax
  omega