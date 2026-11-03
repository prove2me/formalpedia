-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:31.668412+00:00
-- url     : https://prove2.me/submissions/96b32428-15a0-47c1-9b53-baec41f6c601

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K' : SimpleGraph V, H ≤ K' →
      WilliamsonShmoys.HasPlanarDrawingOn K' → K' = H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨F, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
      H hH hmax hcard
  omega