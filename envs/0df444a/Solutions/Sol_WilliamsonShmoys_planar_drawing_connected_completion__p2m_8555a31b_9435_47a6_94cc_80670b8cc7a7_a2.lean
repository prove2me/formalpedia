-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:57.593587+00:00
-- url     : https://prove2.me/submissions/6104f972-ad95-47de-90e9-53d4f6d87a75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And H.Connected (WilliamsonShmoys.HasPlanarDrawingOn H)) := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1 K hK
  exact ⟨H, hKH,
    WilliamsonShmoys.maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1 H hcard hH hmax,
    hH⟩