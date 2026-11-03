-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:13:29.418245+00:00
-- url     : https://prove2.me/submissions/af112125-01b2-49ab-873f-ab73b3da9baa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d G hG hCard
