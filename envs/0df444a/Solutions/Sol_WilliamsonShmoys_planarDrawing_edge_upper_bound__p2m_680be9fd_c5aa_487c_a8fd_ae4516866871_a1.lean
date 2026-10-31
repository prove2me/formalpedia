-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:15.884982+00:00
-- url     : https://prove2.me/submissions/ad3ea0e1-2bfd-498a-a832-aaa8077cc46f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hconn, hH, hle⟩ :=
    WilliamsonShmoys.planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1 K hK hV
  have hbound :=
    WilliamsonShmoys.planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1 H hH hconn hV
  omega