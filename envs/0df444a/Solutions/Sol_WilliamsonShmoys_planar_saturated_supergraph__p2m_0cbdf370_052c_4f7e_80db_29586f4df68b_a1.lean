-- Prove2me | solution 1 for WilliamsonShmoys.planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:02.706562+00:00
-- url     : https://prove2.me/submissions/4b427ac5-776f-43f7-a1fd-4b6b3d1d1dc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hKH, hHplanar, hHmax, hCardMono⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
      K hV hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
      H hV hHplanar hHmax
  exact ⟨H, hKH, hHplanar, hCount, hCardMono⟩