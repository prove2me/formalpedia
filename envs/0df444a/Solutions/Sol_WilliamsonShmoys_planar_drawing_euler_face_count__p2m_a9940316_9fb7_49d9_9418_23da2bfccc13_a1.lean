-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:10.383736+00:00
-- url     : https://prove2.me/submissions/328c92bc-56e8-4fef-ba14-403ad555038e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hconn : T.Connected) :
    ∃ f : ℤ, (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 := by
  refine ⟨2 - (Fintype.card V : ℤ) + (T.edgeSet.ncard : ℤ), ?_⟩
  ring