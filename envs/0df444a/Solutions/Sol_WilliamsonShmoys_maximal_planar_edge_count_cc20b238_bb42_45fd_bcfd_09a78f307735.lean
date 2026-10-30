-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_cc20b238_bb42_45fd_bcfd_09a78f307735
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:37:32.652988+00:00
-- url     : https://prove2.me/submissions/f1627a4b-4ceb-44cf-9080-c57bee6afadb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_repair

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hIncl, hDrawL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count_repair K hCard hDraw
  have hEq : L = K := hMax L hIncl hDrawL
  rw [← hEq]
  exact hCount