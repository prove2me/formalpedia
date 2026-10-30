-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:30:00.391985+00:00
-- url     : https://prove2.me/submissions/77ca7c76-692b-44f5-af17-4abecb42dea1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_equality

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 <= Fintype.card V) :
    ∃ W : SimpleGraph V,
      LE.le U W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_completion_maximal_supergraph U hU
  exact ⟨W, hUW, hW,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_equality W hW hV hmax⟩