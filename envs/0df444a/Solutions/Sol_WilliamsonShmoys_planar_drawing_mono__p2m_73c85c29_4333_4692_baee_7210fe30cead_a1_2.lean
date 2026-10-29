-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_mono__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:37.579895+00:00
-- url     : https://prove2.me/submissions/11a10dc3-e3d3-490e-a37a-b596117ae0f5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hinj, h1, h2⟩ := hH
  exact ⟨p, arc, hinj, fun u v huv hadj => h1 u v huv (hGH hadj),
    fun u v x y huv hxy ha hb hne => h2 u v x y huv hxy (hGH ha) (hGH hb) hne⟩
