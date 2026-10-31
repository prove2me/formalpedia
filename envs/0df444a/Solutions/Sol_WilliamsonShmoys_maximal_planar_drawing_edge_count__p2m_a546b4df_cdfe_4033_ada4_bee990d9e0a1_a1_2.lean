-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:31:02.69612+00:00
-- url     : https://prove2.me/submissions/cd515cc6-e1fe-448c-8f74-2dae4f016f5a

import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → HasPlanarDrawingOn T → T = S) : S.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274 S hDraw hV hMax
