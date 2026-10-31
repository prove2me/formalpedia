-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:20.797078+00:00
-- url     : https://prove2.me/submissions/b2955451-0d56-4247-b585-7c806830469c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
      H hCard hH hmax
  have hne : H ≠ G := by
    intro hEq
    subst H
    omega
  exact ⟨H, hGH, hne, hH⟩