-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:16:26.592028+00:00
-- url     : https://prove2.me/submissions/d56d0c90-0975-474c-81e4-293a5ea4eedf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hstep : ∀ H : SimpleGraph V, G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H →
      ¬ H.Connected → ∃ K : SimpleGraph V, H < K ∧ WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1 G hG
  refine ⟨H, hGH, ?_, hHplanar⟩
  by_contra hHconn
  obtain ⟨K, hHK, hKplanar⟩ := hstep H hGH hHplanar hHconn
  have hKH : K = H := hmax K (le_of_lt hHK) hKplanar
  exact (ne_of_lt hHK) hKH.symm