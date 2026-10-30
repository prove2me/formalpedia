-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_data__p2m_30c809bc_d869_43a8_8404_fcf85ec28b0f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:49.52688+00:00
-- url     : https://prove2.me/submissions/4b6841a9-9dab-4c05-887a-2ebbe98e6764

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_drawable

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) :
    ∃ f : ℤ,
      (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 ∧
      3 * f ≤ 2 * (T.edgeSet.ncard : ℤ) := by
  have hedge : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawable T hT hV
  refine ⟨2 - (Fintype.card V : ℤ) + (T.edgeSet.ncard : ℤ), ?_, ?_⟩ <;> omega