-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:36.99926+00:00
-- url     : https://prove2.me/submissions/bf140f9b-09de-436f-b750-505f634a0602

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X ≤ W := by
  exact WilliamsonShmoys.exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
    U HasPlanarDrawingOn hU