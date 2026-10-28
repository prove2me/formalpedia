-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:32:38.663276+00:00
-- url     : https://prove2.me/submissions/a4a1a74f-4763-4469-95f2-c5a14bb91393
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_of_maximality

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hHDrawing, hSub, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound K hDrawing
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_of_maximality H hHDrawing hMax hCard
  have hMono : K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hSub
  omega