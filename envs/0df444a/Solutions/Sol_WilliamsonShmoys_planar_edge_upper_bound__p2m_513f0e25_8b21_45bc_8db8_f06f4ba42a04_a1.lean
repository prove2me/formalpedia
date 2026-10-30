-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:52:38.517169+00:00
-- url     : https://prove2.me/submissions/ada61a4b-5e5b-41ef-878f-7022a2e3b7b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMPlanar, hMax, hCardMono⟩ :=
    WilliamsonShmoys.maximal_drawable_extension__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
      L hL hCard
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
      M hMPlanar hMax hCard
  have hMbound : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
    omega
  omega