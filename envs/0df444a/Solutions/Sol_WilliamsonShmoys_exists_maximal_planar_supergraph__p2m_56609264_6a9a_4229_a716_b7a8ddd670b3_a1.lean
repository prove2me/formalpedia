-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:40.143471+00:00
-- url     : https://prove2.me/submissions/c0467630-1481-4648-8e4d-ca2dbc2ae462

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d833d204_1cac_48ce_b1ff_fc91bbaabed8_a2
    HasPlanarDrawingOn L hL