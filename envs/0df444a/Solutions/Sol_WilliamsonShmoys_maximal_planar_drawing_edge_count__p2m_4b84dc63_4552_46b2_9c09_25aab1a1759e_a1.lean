-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:50:07.025902+00:00
-- url     : https://prove2.me/submissions/65f88b34-43b4-4f91-9c40-64501876dc0f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hIncl, hLDraw, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1
      K hV hDraw
  have hEq : L.edgeSet = K.edgeSet := hMax L hIncl hLDraw
  rw [hEq] at hCount
  exact hCount