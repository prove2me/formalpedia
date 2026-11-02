-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:57:04.914412+00:00
-- url     : https://prove2.me/submissions/1c756bd6-215d-4c4c-a2a7-67438b6f214c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1
import Theorems.Thm_simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) :
    ∃ H : SimpleGraph V,
      P ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by
  classical
  let Q : SimpleGraph V → Prop := fun H => P ≤ H ∧ HasPlanarDrawingOn H
  have hQ : ∃ H, Q H := ⟨P, le_rfl, hP⟩
  obtain ⟨H, hHQ, hmax⟩ :=
    finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1
      Q (fun G => G.edgeSet.ncard)
      (by
        intro G K hGK hne
        exact simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3
          G K hGK hne)
      hQ
  refine ⟨H, hHQ.1, hHQ.2, ?_⟩
  intro K hHK hKplanar
  exact (hmax K ⟨le_trans hHQ.1 hHK, hKplanar⟩ hHK)