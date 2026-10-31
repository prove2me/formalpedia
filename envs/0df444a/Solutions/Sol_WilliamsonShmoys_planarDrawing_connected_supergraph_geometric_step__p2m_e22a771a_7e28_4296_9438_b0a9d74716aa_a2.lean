-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:43.75172+00:00
-- url     : https://prove2.me/submissions/5a89d318-05a9-44d4-9c3a-fe57bbea548d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_disconnected_edge_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a1

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
  classical
  by_cases hconn : K.Connected
  · exact ⟨K, le_rfl, hconn, hK, le_rfl⟩
  · obtain ⟨H, hKH, hHconn, hHdraw, hEdges⟩ :=
      WilliamsonShmoys.planarDrawing_disconnected_edge_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a1
        K hK hV hconn
    refine ⟨H, hKH, hHconn, hHdraw, ?_⟩
    calc
      K.edgeSet.ncard ≤ K.edgeSet.ncard + 1 := Nat.le_add_right _ _
      _ = H.edgeSet.ncard := hEdges.symm
