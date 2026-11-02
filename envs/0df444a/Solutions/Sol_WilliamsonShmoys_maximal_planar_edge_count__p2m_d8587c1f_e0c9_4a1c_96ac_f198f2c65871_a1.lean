-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:10.543955+00:00
-- url     : https://prove2.me/submissions/8676661e-72b2-4fa2-bc5b-f76ed5bb39e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V)
    [DecidableRel P.Adj] :
    P.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1 P hP hcard
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1 P hP hmax hcard
  exact Nat.le_antisymm hu hl