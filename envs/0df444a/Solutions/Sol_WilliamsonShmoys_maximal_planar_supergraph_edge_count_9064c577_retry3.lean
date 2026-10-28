-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:42:54.927735+00:00
-- url     : https://prove2.me/submissions/205d2da1-f0d3-43ae-881c-020832a3200e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3 K hDraw hCard
  have hLK : L <= K := hMax L hKL hLDraw
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hCount