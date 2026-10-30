-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:55:38.786301+00:00
-- url     : https://prove2.me/submissions/b8dbad5e-89d7-475c-9fd6-17d28472d292
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hSub, hKDraw, hCount⟩ :=
    WilliamsonShmoys.exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1
      H hDraw hV
  have hEq : K.edgeSet = H.edgeSet := hMax K hSub hKDraw
  rw [← hEq]
  exact hCount