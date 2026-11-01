-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:13.82256+00:00
-- url     : https://prove2.me/submissions/55e35ce7-64a1-42f6-bb20-d2c1c555e936

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
import Theorems.Thm_WilliamsonShmoys_strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1 H hH
  refine ⟨K, hHK, hK, ?_⟩
  intro L hKL hL
  by_contra hne
  have hneq : K ≠ L := fun heq => hne heq.symm
  have hlt :=
    WilliamsonShmoys.strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1 hKL hneq
  exact (not_lt_of_ge (hmax L (le_trans hHK hKL) hL)) hlt