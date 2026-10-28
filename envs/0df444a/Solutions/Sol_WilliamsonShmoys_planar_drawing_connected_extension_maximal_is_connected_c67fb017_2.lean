-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension_maximal_is_connected_c67fb017
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:02:23.763533+00:00
-- url     : https://prove2.me/submissions/5ec6ef93-018a-4564-85f2-9db4bc0a3368
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_edge_extension_ge_three

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.Connected := by
  by_contra hDisconnected
  obtain ⟨K, hHK, hKPlanar, hNotKH⟩ :=
    WilliamsonShmoys.planar_drawing_disconnected_edge_extension_ge_three
      H hH hV hDisconnected
  exact hNotKH (hmax K hHK hKPlanar)