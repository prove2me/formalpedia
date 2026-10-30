-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:51:50.718379+00:00
-- url     : https://prove2.me/submissions/84d12d16-ff91-47ad-959c-971d20e01acd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hHdraw, hHconn, hmono⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1 G hG hCard
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1 H hHdraw hHconn hCard
  omega