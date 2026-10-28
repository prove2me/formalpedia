-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:06:39.65202+00:00
-- url     : https://prove2.me/submissions/23230e12-69bb-440a-a614-62f4947e720f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_proper_supergraph_of_disconnected_planar
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_proper_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.Connected ∧
      P ≤ Q := by
  exact WilliamsonShmoys.planar_connected_supergraph_of_proper_augmentation
    P hCard hP (by
      intro G hG hGnc
      exact WilliamsonShmoys.planar_proper_supergraph_of_disconnected_planar
        G hCard hG hGnc)
