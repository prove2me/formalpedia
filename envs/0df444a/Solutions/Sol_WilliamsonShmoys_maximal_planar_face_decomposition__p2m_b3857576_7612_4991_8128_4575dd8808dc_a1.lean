-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:46:04.617951+00:00
-- url     : https://prove2.me/submissions/c0b3ab4c-2b59-4533-b975-427ac6127892
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hConn :
      M.Connected :=
    WilliamsonShmoys.maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
      M hM hMax hV
  have hEdges :
      M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
      M hM hMax hConn hV
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega