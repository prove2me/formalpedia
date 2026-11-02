-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:44:13.587465+00:00
-- url     : https://prove2.me/submissions/d0b0e827-bc79-4873-b6b6-ebd2f4a9798e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  obtain ⟨M, hLM, hPM, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1
      (α := SimpleGraph V)
      (P := fun G => L ≤ G ∧ HasPlanarDrawingOn G)
      (s := L)
      (hP := ⟨le_rfl, hL⟩)
  rcases hPM with ⟨_, hM⟩
  refine ⟨M, hLM, hM, ?_⟩
  intro N hMN hN
  exact hmax N hMN ⟨le_trans hLM hMN, hN⟩