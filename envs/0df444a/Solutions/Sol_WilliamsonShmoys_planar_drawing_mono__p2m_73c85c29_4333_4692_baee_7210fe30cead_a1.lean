-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_mono__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:11:34.916049+00:00
-- url     : https://prove2.me/submissions/cde7ad51-9824-407b-b3c5-6aed37a6b039

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv h => h1 u v huv (hGH h),
    fun u v x y huv hxy h h' => h2 u v x y huv hxy (hGH h) (hGH h')⟩
