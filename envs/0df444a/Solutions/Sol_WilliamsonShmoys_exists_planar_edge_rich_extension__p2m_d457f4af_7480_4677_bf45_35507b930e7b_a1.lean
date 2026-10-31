-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:10.966287+00:00
-- url     : https://prove2.me/submissions/f974d801-04b4-4234-ac91-950113bac218

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_has_dense_supergraph H hDraw hV
