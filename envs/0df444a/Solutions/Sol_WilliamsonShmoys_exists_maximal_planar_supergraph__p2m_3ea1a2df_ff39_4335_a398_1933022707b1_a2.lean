-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:05.214802+00:00
-- url     : https://prove2.me/submissions/6347bf48-f16c-4697-a6d7-72c30fda1e0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) H hHdraw