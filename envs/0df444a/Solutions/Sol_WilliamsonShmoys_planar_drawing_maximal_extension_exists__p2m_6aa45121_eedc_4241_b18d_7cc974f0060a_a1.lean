-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:43:04.623481+00:00
-- url     : https://prove2.me/submissions/c6f399b8-3533-492d-afb3-664bd127bec0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M := by
  classical
  obtain ⟨M, hM, hLM, hmax⟩ :=
    exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1
      (α := SimpleGraph V)
      (P := fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      L ⟨le_rfl, hL⟩
  refine ⟨M, hLM, hM.2, ?_⟩
  intro K hMK hK
  exact hmax K hMK ⟨le_trans hLM hMK, hK⟩