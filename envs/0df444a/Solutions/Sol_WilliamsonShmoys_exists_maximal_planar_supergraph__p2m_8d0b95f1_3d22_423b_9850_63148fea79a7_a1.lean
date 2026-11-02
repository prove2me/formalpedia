-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:44:36.120562+00:00
-- url     : https://prove2.me/submissions/1f694730-a809-4037-b66b-9056e5c64438

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKDrawing : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let S : Set (SimpleGraph V) := {L | K ≤ L ∧ HasPlanarDrawingOn L}
  have hSfinite : S.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro G hG
      exact Set.mem_univ G)
  have hSne : S.Nonempty := ⟨K, le_rfl, hKDrawing⟩
  obtain ⟨L, hL⟩ := hSfinite.exists_maximal hSne
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro M hLM hMdraw
  have hM : M ∈ S := ⟨hL.1.1.trans hLM, hMdraw⟩
  have hML : M ≤ L := hL.2 hM hLM
  exact le_antisymm hML hLM