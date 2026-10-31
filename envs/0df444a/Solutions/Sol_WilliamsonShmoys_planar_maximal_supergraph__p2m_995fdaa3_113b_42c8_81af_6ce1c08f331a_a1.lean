-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:07.242471+00:00
-- url     : https://prove2.me/submissions/c5d4a3ca-956e-4eea-a40b-6f4473d1f568

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1

set_option autoImplicit false

/-- Every drawable graph extends to an edge-maximal drawable graph on the same finite vertex type. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet = N.edgeSet := by
  classical
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  have hmono : ∀ {A B : SimpleGraph V}, B.edgeSet ⊆ A.edgeSet → P A → P B := by
    intro A B hsub hA
    exact WilliamsonShmoys.planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1 hsub hA
  exact finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1 M P hmono hDraw