-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:01.584213+00:00
-- url     : https://prove2.me/submissions/4179756d-1d90-49a9-81bf-c28f7b996108

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
import Theorems.Thm_simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop := fun L => K ≤ L ∧ HasPlanarDrawingOn L
  obtain ⟨L, hL, hmax⟩ :=
    finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
      P (fun A B : SimpleGraph V => A ≤ B)
      (fun A : SimpleGraph V => A.edgeFinset.card)
      ⟨K, le_rfl, hK⟩
      (by
        intro A B hA hB hAB hne
        exact simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
          A B hAB hne)
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  exact (hmax M ⟨le_trans hL.1 hLM, hM⟩ hLM).symm
