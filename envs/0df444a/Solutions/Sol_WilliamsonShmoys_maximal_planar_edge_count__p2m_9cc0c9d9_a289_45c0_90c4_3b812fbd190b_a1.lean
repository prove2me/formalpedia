-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:24:24.402993+00:00
-- url     : https://prove2.me/submissions/8b2efc34-e520-4c62-9411-1ad0891a633a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨K, hMK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
      M hM hV
  have hKM : K = M := hmax K hMK hK
  rw [hKM] at hcount
  exact le_of_eq hcount.symm