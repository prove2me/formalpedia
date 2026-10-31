-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:29.439857+00:00
-- url     : https://prove2.me/submissions/24baae10-b664-4314-a709-8638d5e816e5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
import Theorems.Thm_WilliamsonShmoys_simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ R) ∧
      Q.edgeSet.ncard ≤ R.edgeSet.ncard := by
  obtain ⟨R, hQR, hRDraw, hMax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
      Q hDraw
  refine ⟨R, hQR, hRDraw, ?_, ?_⟩
  · intro S hRS hSDraw
    exact WilliamsonShmoys.simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
      R S hRS (hMax S (le_trans hQR hRS) hSDraw)
  · exact hMax Q le_rfl hDraw