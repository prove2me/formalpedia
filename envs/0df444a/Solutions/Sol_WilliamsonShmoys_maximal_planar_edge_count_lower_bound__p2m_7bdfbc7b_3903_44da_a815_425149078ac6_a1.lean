-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:15:01.964827+00:00
-- url     : https://prove2.me/submissions/1a7e7435-33e1-4833-bb7d-4d7681b24feb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [instH : DecidableRel H.Adj]
    (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    3 * Fintype.card V <= H.edgeFinset.card + 6 := by
  have hinst : instH = Classical.decRel H.Adj := Subsingleton.elim _ _
  cases hinst
  exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
    H hcard hH hmax
