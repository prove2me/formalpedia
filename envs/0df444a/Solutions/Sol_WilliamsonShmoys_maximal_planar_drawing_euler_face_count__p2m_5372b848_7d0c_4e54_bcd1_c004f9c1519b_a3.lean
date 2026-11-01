-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:27.724782+00:00
-- url     : https://prove2.me/submissions/0d46bed8-791a-4543-adbf-1f91faf653e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_b975264c_a647_4729_9e53_57cc5272b06f_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [DecidableRel L.Adj] (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeFinset.card + 2 ∧
      3 * f = 2 * L.edgeFinset.card := by
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b975264c_a647_4729_9e53_57cc5272b06f_a1
      L hL hcard hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega