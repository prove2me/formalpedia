-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected_for_euler_equations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:01:37.601988+00:00
-- url     : https://prove2.me/submissions/d8b5e487-5b0d-4bed-b2e3-135ae47e34b1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_disconnected
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) : L.Connected := by
  classical
  by_contra hDisconnected
  obtain ⟨M, hLM, hM, hNe⟩ :=
    WilliamsonShmoys.planar_augmentation_of_disconnected L hL hCard hDisconnected
  exact hNe (hMax M hLM hM)