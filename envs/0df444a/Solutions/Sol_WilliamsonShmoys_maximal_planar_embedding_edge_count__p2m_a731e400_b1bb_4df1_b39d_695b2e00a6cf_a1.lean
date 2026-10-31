-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:20.949991+00:00
-- url     : https://prove2.me/submissions/f1c0bb16-c850-476f-91f5-208ce7a2cb74

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) : T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hTN, hNDraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1 T hV hDraw
  have hNT : N <= T := hMax N hTN hNDraw
  have hEq : N = T := le_antisymm hNT hTN
  rw [hEq] at hCount
  exact hCount