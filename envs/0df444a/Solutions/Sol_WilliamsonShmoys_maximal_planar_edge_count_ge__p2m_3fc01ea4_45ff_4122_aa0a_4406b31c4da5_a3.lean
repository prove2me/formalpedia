-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:30:43.72844+00:00
-- url     : https://prove2.me/submissions/df2bc18a-1a51-48c5-8e38-fc1a638e3b1b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  by_contra hnot
  have hsmall : H.edgeFinset.card < 3 * Fintype.card V - 6 := by omega
  obtain ⟨J, hHJ, hJdraw, hstrict⟩ :=
    WilliamsonShmoys.planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2
      H hcard hHconn hHdraw hsmall
  exact hstrict (hHmax J hHJ hJdraw)
