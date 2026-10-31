-- Prove2me | solution 1 for WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:50.584034+00:00
-- url     : https://prove2.me/submissions/6c4c852b-cdfe-4083-a86c-b3a95971a629

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hEdges, hMono⟩ :=
    WilliamsonShmoys.planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
      K hV hK
  omega