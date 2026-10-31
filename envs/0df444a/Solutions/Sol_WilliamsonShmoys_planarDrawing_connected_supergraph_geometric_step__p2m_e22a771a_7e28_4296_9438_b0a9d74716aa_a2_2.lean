-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:54.679071+00:00
-- url     : https://prove2.me/submissions/9a793c00-6fad-418c-9013-38965b4b5cf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  by_cases hconn : K.Connected
  · exact ⟨K, le_rfl, hconn, hK, le_rfl⟩
  · obtain ⟨H, hKH, hHconn, hHdraw⟩ :=
      WilliamsonShmoys.planarDrawing_disconnected_supergraph_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a3
        K hK hV hconn
    exact ⟨H, hKH, hHconn, hHdraw, Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)⟩