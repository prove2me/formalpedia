-- Prove2me | solution 1 for WilliamsonShmoys.planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:26.98666+00:00
-- url     : https://prove2.me/submissions/60c30387-eeee-4191-a3bc-c2f7045454d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, instH, hH, hsub, hmax, hcard⟩ :=
    WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2
      K hK hconn hn
  letI : DecidableRel H.Adj := instH
  have hHcard : H.edgeFinset.card = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2
      H hH hmax hn
  exact hcard.trans (le_of_eq hHcard)