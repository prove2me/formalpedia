-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:27.788231+00:00
-- url     : https://prove2.me/submissions/3fbf42ce-31ab-4467-957b-8d2170cec0df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     2 * G.edgeFinset.card + 12 ≤ 6 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
      G hG hmax hcard
  omega