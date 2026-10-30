-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:58.536977+00:00
-- url     : https://prove2.me/submissions/47a0b24f-edde-4de5-9b30-d08e3910971e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V) : P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Q, hPQ, hQDraw, hQMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 P hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 Q hQDraw hQMax hV
  have hMono :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 P Q hPQ
  omega