-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:49:24.473896+00:00
-- url     : https://prove2.me/submissions/a2451f05-75db-474f-b547-df2e25084c59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet → HasPlanarDrawingOn G → G.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hSub, hK, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1
      H hH hCard
  have hEq := hMax K hSub hK
  simpa [hEq] using hCount