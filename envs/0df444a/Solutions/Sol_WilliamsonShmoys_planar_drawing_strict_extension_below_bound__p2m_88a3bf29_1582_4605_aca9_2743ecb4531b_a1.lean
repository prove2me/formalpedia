-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:41.736317+00:00
-- url     : https://prove2.me/submissions/4b8508b5-c398-4134-80f3-d953e0be5b68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V, G ≤ M ∧ M ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  obtain ⟨M, hGM, hMdraw, hMcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1
      G hDraw hV
  have hneq : M ≠ G := by
    intro hEq
    subst M
    omega
  exact ⟨M, hGM, hneq, hMdraw⟩