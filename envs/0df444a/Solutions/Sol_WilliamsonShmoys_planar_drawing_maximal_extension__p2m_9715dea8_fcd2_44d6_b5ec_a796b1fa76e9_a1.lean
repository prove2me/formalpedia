-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:36.269377+00:00
-- url     : https://prove2.me/submissions/c1ad2487-cd8c-44bc-943e-88852936aeb7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  let S : Set (SimpleGraph V) := {M | L ≤ M ∧ HasPlanarDrawingOn M}
  have hS : S.Nonempty := by
    refine ⟨L, ?_⟩
    change L ≤ L ∧ HasPlanarDrawingOn L
    exact ⟨le_rfl, hL⟩
  obtain ⟨M, hM, hmax⟩ :=
    finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1 S hS
  change L ≤ M ∧ HasPlanarDrawingOn M at hM
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  apply hmax N hMN
  change L ≤ N ∧ HasPlanarDrawingOn N
  exact ⟨hM.1.trans hMN, hN⟩