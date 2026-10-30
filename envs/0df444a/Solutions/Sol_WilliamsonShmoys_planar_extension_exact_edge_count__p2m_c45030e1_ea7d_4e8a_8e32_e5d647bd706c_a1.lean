-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:10:41.101935+00:00
-- url     : https://prove2.me/submissions/df0dbdcd-5e07-417d-b3fd-3d2e4b2140cb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hGM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
      G hG
  exact ⟨M, hGM,
    hM,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
      M hV hM hmax⟩