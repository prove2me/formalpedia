-- Prove2me | solution 1 for WilliamsonShmoys.augmentation_maximal_drawable_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:22:08.983046+00:00
-- url     : https://prove2.me/submissions/f07c4797-cd15-489d-946f-77ec7266844d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_has_drawable_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hdraw : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.Connected := by
  by_contra hconn
  obtain ⟨K, hHK, hKdraw, hneq⟩ :=
    WilliamsonShmoys.disconnected_drawable_has_drawable_extension H hdraw hV hconn
  exact hneq (hmax K hHK hKdraw)
