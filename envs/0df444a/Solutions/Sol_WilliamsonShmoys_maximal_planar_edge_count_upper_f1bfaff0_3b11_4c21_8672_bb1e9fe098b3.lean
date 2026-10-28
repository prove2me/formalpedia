-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:54:03.93941+00:00
-- url     : https://prove2.me/submissions/9e883fc2-b6b5-4d8a-9e80-d30c041267be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hHcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph G hG hCard
  have hEdges : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
    apply Set.ncard_le_ncard
    · exact hGH
    · exact Set.toFinite H.edgeSet
  omega