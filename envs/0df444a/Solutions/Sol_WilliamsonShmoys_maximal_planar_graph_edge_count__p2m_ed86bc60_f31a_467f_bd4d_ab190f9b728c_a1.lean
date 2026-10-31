-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:46.333813+00:00
-- url     : https://prove2.me/submissions/a56c1cbd-af3b-4d0d-b8bf-0b350f6d4a07

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1 L hDraw hV
  have hNotBelow : ¬ L.edgeSet.ncard < 3 * Fintype.card V - 6 := by
    intro hBelow
    obtain ⟨M, hSub, hNe, hMDraw⟩ :=
      WilliamsonShmoys.planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
        L hDraw hV hBelow
    exact hNe (hMax M hSub hMDraw)
  exact (Nat.le_antisymm hUpper (Nat.le_of_not_gt hNotBelow)).symm