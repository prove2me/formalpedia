-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_from_euler__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:58.065769+00:00
-- url     : https://prove2.me/submissions/5241392c-74fe-4c77-b7b5-7c07112c3020

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulating_planar_supergraph__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
import Theorems.Thm_WilliamsonShmoys_edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hSub, hH, hCount⟩ :=
    WilliamsonShmoys.exists_triangulating_planar_supergraph__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
      G hConn hV hG
  exact WilliamsonShmoys.edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
    G H hSub hCount