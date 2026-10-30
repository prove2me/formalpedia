-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_retry_49abde41
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:42:11.177805+00:00
-- url     : https://prove2.me/submissions/43ae4ab2-b68f-439e-9d5f-d041b1a35f87

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_retry_49abde41
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_retry_49abde41

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_retry_49abde41 H hH hCard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_49abde41 H hH hmax hCard
  linarith