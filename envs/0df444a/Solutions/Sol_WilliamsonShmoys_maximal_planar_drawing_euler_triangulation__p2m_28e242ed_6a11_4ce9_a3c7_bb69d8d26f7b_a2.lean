-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:18.722759+00:00
-- url     : https://prove2.me/submissions/ea477456-898b-412f-b230-5fd1a1e770bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    ∃ f : ℕ, Fintype.card V + f = L.edgeFinset.card + 2 ∧
      2 * L.edgeFinset.card = 3 * f := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hE := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
    L hL hmax hcard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega