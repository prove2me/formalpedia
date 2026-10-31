-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_ec87f3de_339b_432c_a6c1_ac3963609395_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:26.681387+00:00
-- url     : https://prove2.me/submissions/a5f167c4-0eb6-4a7b-a7df-f0aa852e7a47

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hNQ, hQ, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
      N hDraw
  exact ⟨Q, hNQ, hQ,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
      Q hV hQ hmax⟩