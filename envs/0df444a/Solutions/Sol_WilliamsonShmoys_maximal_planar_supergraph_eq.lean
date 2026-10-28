-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:40.256498+00:00
-- url     : https://prove2.me/submissions/f0737004-e3b1-4281-a674-165d7f0b4a49

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H J : SimpleGraph V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → K = H)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hHJ : ∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) :
    J = H := by
  exact hmax J hJ hHJ
