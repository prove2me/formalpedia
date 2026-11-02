-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:16:00.116253+00:00
-- url     : https://prove2.me/submissions/277daca6-4d7e-4602-ae3a-11a3b6c96caa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hPK : P K := ⟨le_rfl, hK⟩
  obtain ⟨L, hKL, hPL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1
      P K hPK
  refine ⟨L, hPL.1, hPL.2, ?_⟩
  intro M hLM hM
  exact hmax M hLM ⟨hKL.trans hLM, hM⟩