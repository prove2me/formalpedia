-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:29:46.441854+00:00
-- url     : https://prove2.me/submissions/e9a2998f-1ece-4ce3-bb01-7095d740d4c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_for_certificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_certificate

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) (hCard : 3 ≤ Fintype.card V) :
    ∃ f b : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      b = 2 * K.edgeSet.ncard ∧
      3 * f ≤ b := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation_for_certificate K hKdraw hconn
  refine ⟨f, 2 * K.edgeSet.ncard, hf, rfl, ?_⟩
  have he :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_certificate K hKdraw hconn hCard
  omega