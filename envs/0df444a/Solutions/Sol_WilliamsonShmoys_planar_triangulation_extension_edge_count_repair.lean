-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count_repair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:02:09.612737+00:00
-- url     : https://prove2.me/submissions/2bf0151e-4380-49c2-b3a5-1283027700ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exists_maximal
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_edge_count

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_exists_maximal K hCard hDraw
  refine ⟨L, hKL, hDrawL, ?_⟩
  exact WilliamsonShmoys.planar_triangulation_maximal_edge_count L hCard hDrawL hMax