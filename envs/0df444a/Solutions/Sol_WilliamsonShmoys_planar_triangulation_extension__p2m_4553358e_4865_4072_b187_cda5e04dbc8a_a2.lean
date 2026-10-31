-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:26.98118+00:00
-- url     : https://prove2.me/submissions/65d7c5df-82ee-4894-a43b-d583a1b3c416

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJplanar, hJmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
      H hV hH
  refine ⟨J, hHJ, hJplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
    J hV hJplanar hJmax