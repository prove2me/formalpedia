-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_edge_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:52:09.550259+00:00
-- url     : https://prove2.me/submissions/dfcbcfb1-276d-40d8-96bd-d4d3ce20a449
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_edge_witness

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H := by
  obtain ⟨K, hHK, hPlanar, u, v, hNotAdj, hAdj⟩ :=
    WilliamsonShmoys.planar_disconnected_edge_witness H hH hDisconnected
  refine ⟨K, hHK, hPlanar, ?_⟩
  intro hKH
  exact hNotAdj (hKH hAdj)