-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:09.714146+00:00
-- url     : https://prove2.me/submissions/878e7309-6332-4952-9ee2-3c44e738b2f1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z → HasPlanarDrawingOn Z → Z ≤ Y := by
  classical
  let P : SimpleGraph V → Prop := fun G => X ≤ G ∧ HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨X, le_rfl, hX⟩
  obtain ⟨Y, hPY, hMax⟩ :=
    exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1 P hP
  rcases hPY with ⟨hXY, hY⟩
  refine ⟨Y, hXY, hY, ?_⟩
  intro Z hYZ hZ
  have hPZ : P Z := ⟨hXY.trans hYZ, hZ⟩
  exact hMax Z hPZ hYZ