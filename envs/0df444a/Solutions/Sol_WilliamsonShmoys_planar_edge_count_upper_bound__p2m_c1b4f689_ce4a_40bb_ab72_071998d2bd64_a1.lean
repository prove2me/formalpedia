-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:24.501477+00:00
-- url     : https://prove2.me/submissions/fb3e282e-e95e-4f0f-9af1-55c652062d00

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 ≤ Fintype.card V)
    [DecidableRel P.Adj] :
    P.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨H, hPH, hH, hmax, hcard_mono⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2 P hP
  have hHbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2 H hH hcard hmax
  have hle : P.edgeFinset.card ≤ H.edgeFinset.card := hcard_mono
  omega
