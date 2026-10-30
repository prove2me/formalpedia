-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:36.504418+00:00
-- url     : https://prove2.me/submissions/891ad119-0923-4928-afc6-2e98567ea31a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.Connected := by
  by_contra hdisconnected
  obtain ⟨K, hHK, hKplanar, hKneH⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_planar_extension__p2m_b968de7a_bb4e_4b2a_a58b_cf3030ff5cd1_a2
      H hplanar hV hdisconnected
  exact hKneH (hmax K hHK hKplanar)
