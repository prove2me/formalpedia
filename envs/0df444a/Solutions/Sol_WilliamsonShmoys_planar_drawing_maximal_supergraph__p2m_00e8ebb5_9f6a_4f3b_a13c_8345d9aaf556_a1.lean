-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:03.915988+00:00
-- url     : https://prove2.me/submissions/5dfea319-a29e-4cda-9deb-40b2301a5918

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → H.edgeSet = K.edgeSet := by
  let P : SimpleGraph V → Prop := fun G =>
    HasPlanarDrawingOn G ∧ M.edgeSet ⊆ G.edgeSet
  obtain ⟨H, hHP, hmax⟩ :=
    finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1
      P ⟨M, hDraw, Set.Subset.rfl⟩
  refine ⟨H, hHP.2, hHP.1, ?_⟩
  intro K hHK hKDraw
  exact hmax K ⟨hKDraw, hHP.2.trans hHK⟩ hHK