-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:45.819275+00:00
-- url     : https://prove2.me/submissions/df5bcb02-d112-4ca8-aaad-10af930669c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    Exists fun H : SimpleGraph V =>
      And (Set.Subset K.edgeSet H.edgeSet)
        (And (HasPlanarDrawingOn H)
          (H.edgeSet.ncard = 3 * Fintype.card V - 6)) := by
  obtain ⟨H, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8 K hK
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
      K H hV hsub hdraw hmax
  refine ⟨H, hsub, hdraw, ?_⟩
  omega
