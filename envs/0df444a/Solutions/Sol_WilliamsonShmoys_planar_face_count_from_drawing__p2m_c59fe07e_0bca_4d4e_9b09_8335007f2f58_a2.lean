-- Prove2me | solution 1 for WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:34:04.202239+00:00
-- url     : https://prove2.me/submissions/006c8d5a-226b-446a-883a-1c1c19e79e67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + (f : ℤ) = 2 ∧
      (3 : ℤ) * (f : ℤ) ≤ 2 * (K.edgeSet.ncard : ℤ) := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
      K hconn hK
  refine ⟨f, hEuler, ?_⟩
  have hEdge :=
    WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
      K hcard hconn hK
  omega
