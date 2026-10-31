-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:00:29.493337+00:00
-- url     : https://prove2.me/submissions/358cc164-a6ce-4a1c-9174-eba05217bd0b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_drawing_has_triangulation G hG hCard
