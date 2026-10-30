-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_64cb9f36
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:02:24.998984+00:00
-- url     : https://prove2.me/submissions/1c4b1dd7-35aa-41bc-a4b2-18e02c2013cb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_20261026
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_lower_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hPmax : ∀ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Q) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_20261026 P hP hV
  have hLower :=
    WilliamsonShmoys.planar_drawing_edge_count_lower_20261026 P hP hV hPmax
  omega