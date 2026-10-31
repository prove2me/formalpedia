-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:49.263429+00:00
-- url     : https://prove2.me/submissions/e950d9a4-982d-4da5-80a9-b12e870b4a35

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = Z := by
  classical
  let P : SimpleGraph V → Prop := fun G =>
    Y ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hP : ∃ G : SimpleGraph V, P G := ⟨Y, le_rfl, hY⟩
  obtain ⟨Z, hZ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1 P hP
  refine ⟨Z, hZ.1, hZ.2, ?_⟩
  intro W hZW hW
  apply hmax W
  · exact ⟨le_trans hZ.1 hZW, hW⟩
  · exact hZW