-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_for_certificate_38ffb807
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:40:21.862222+00:00
-- url     : https://prove2.me/submissions/32d7bf1a-3f51-4cdf-8977-6935f0016a1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_pair_extension_cert38ffb807
import Theorems.Thm_WilliamsonShmoys_finite_extension_by_pair_connections_cert38ffb807

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.finite_extension_by_pair_connections_cert38ffb807
      K hV WilliamsonShmoys.HasPlanarDrawingOn hdraw
      (by
        intro G hKG hGdraw u v huv hnot
        obtain ⟨H, hGH, hHdraw, hreach⟩ :=
          WilliamsonShmoys.planar_drawing_pair_extension_cert38ffb807
            G hGdraw u v huv hnot
        exact ⟨H, hGH, hHdraw, hreach⟩)
  exact ⟨H, hKH, hHconn, hHdraw⟩