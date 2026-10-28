-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:32.912164+00:00
-- url     : https://prove2.me/submissions/ac3572ad-a006-42c2-9684-ca8596e19302

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hadj => h1 u v huv (hGH hadj),
    fun u v x y huv hxy h3 h4 hne => h2 u v x y huv hxy (hGH h3) (hGH h4) hne⟩
