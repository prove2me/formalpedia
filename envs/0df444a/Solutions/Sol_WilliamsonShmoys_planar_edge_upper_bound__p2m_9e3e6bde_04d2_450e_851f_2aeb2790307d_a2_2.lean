-- Prove2me | solution 2 for WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:08:48.188952+00:00
-- url     : https://prove2.me/submissions/e5ea7b1f-8bd1-4755-b2c3-c7c9f43a16ee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5
  | (apply _root_.WilliamsonShmoys.planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5 <;> assumption)
