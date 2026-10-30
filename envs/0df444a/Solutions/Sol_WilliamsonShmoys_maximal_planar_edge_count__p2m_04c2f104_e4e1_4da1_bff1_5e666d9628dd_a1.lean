-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:34:31.326544+00:00
-- url     : https://prove2.me/submissions/ef33ee90-8874-452d-8d6a-7e8ecc6b3d4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      Set.Subset H.edgeSet K.edgeSet →
      H.edgeSet = K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2
      H hH hmax hV
  nlinarith