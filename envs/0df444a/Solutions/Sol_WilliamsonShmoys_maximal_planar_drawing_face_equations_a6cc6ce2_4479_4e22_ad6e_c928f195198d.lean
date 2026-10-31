-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:41:55.520474+00:00
-- url     : https://prove2.me/submissions/94ff0383-8bda-41ab-aa14-81e931810f16

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_counting_equations

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard :=
  WilliamsonShmoys.maximal_drawable_face_counting_equations M hM hMax hCard
