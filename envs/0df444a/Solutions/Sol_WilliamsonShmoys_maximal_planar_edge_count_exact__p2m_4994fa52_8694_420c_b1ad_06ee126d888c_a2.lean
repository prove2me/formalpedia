-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:29.996239+00:00
-- url     : https://prove2.me/submissions/1b9db250-3012-45c8-a676-8b873a5a5bab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_planar_upper_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ (J : SimpleGraph V),
      G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.maximal_planar_edge_count_planar_upper_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1 G hG hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1 G hG hmax hcard
  omega