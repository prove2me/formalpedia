-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:14.38236+00:00
-- url     : https://prove2.me/submissions/3205b744-9037-47e2-b7fe-251a85d47d22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
import Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2

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
  exact WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
    (P := HasPlanarDrawingOn) (K := K) hV hK
    (fun G hG hGcard hD =>
      WilliamsonShmoys.planarDrawing_add_bridge__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
        G hG hGcard hD)
    hDisconnected