-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound_connected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:42:07.467655+00:00
-- url     : https://prove2.me/submissions/18607fc1-8b1c-4464-8644-6ca00d642910
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hsub, hdrawK, hmax, hcard_le⟩ :=
    WilliamsonShmoys.planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
      H hcard hconn hdraw
  have hbound :=
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
      K hcard hdrawK hmax
  omega