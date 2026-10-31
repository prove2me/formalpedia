-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:23.966684+00:00
-- url     : https://prove2.me/submissions/b62fd49b-eb7b-49c4-93b7-641819596dce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
      H hPlanar
  exact ⟨J, hHJ, hJPlanar,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
      J hJPlanar hV hMax⟩