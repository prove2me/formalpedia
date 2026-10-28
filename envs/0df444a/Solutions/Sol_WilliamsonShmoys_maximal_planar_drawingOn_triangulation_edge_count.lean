-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:34:40.947435+00:00
-- url     : https://prove2.me/submissions/6f43c1a5-f0b8-49da-9c4f-6cad37ad14c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulated_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨S, hRS, hS, hCount⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph R hCard hR
  have hEq : S = R := hMax S hRS hS
  simpa [hEq] using hCount