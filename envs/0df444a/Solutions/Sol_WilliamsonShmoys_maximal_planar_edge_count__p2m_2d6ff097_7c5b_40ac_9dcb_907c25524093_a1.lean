-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:27.812241+00:00
-- url     : https://prove2.me/submissions/5805bce1-832a-410f-8ad1-1044ed8e9b2e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V,
      (forall {u v : V}, Q.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      R = Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    3 * Fintype.card V = Q.edgeFinset.card + 6 := by
  letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
    Q hcard hQ
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
    Q hcard hQ hmax
  omega