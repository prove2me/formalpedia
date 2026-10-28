-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_le_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:06:03.319298+00:00
-- url     : https://prove2.me/submissions/d7f2f8b7-6336-469a-a6db-67bbfec61836
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_bound_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_bound_maximal_drawing_count
import Theorems.Thm_WilliamsonShmoys_edge_bound_edge_count_monotone

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDrawH, hMax⟩ :=
    edge_bound_exists_maximal_extension K hDraw
  have hCount := edge_bound_maximal_drawing_count H hDrawH hMax hCard
  have hMono := edge_bound_edge_count_monotone hKH
  omega