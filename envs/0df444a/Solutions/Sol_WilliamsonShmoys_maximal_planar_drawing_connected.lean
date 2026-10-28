-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:11:41.211949+00:00
-- url     : https://prove2.me/submissions/4df7ce51-35c7-428b-8236-ef5eed75435d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_of_not_connected

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.Connected := by
  by_contra hnot
  obtain ⟨K, hHK, hKH, hK⟩ :=
    WilliamsonShmoys.planar_extension_of_not_connected H hH hnot
  exact hKH (hmax K hHK hK)