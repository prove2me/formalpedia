-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:27.985895+00:00
-- url     : https://prove2.me/submissions/acb51538-8f2d-4843-93d0-4dbfd89f9af2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V}
    (hAB : A ≤ B)
    (hB : WilliamsonShmoys.HasPlanarDrawingOn B) :
    WilliamsonShmoys.HasPlanarDrawingOn A := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hB
  exact ⟨p, arc, hp, fun u v huv hadj => h1 u v huv (hAB hadj),
    fun u v x y huv hxy h3 h4 hne => h2 u v x y huv hxy (hAB h3) (hAB h4) hne⟩
