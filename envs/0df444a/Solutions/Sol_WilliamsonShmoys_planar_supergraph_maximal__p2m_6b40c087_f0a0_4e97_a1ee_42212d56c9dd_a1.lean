-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:11.696512+00:00
-- url     : https://prove2.me/submissions/f60e8fd5-187c-4449-890f-0ca29eb9e1f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) := by
  exact finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1
    HasPlanarDrawingOn G hG