-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:05.505493+00:00
-- url     : https://prove2.me/submissions/6287bd1f-9d62-4f6f-b8ba-bbc22fdcf675
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
import Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
    K hK (fun G hG hD =>
      WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a1
        G hG hD) hDisconnected