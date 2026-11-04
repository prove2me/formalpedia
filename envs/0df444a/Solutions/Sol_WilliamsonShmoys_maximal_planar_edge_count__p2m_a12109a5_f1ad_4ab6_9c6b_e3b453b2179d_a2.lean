-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:44.657167+00:00
-- url     : https://prove2.me/submissions/e604b2bb-8b52-496d-9a86-a56848f4aa81

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1 N hV hN
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1 N hV hN hmax
  omega
