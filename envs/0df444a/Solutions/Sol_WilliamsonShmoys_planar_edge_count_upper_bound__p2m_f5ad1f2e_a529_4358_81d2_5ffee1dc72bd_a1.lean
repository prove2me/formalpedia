-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:21.203114+00:00
-- url     : https://prove2.me/submissions/6adda053-8f6d-4691-9c42-de5bb6fd5d30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hLH, hconn, hH⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
      L hL hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
      H hH hconn hcard
  have hsub : L.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hLH
  have hle : L.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hsub
  omega