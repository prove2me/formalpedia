-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_completion_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:45:44.45958+00:00
-- url     : https://prove2.me/submissions/d54bda0b-80d6-4e0b-b5a9-aa69227ac0a8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_c3d7847a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_c3d7847a

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hSub, hJDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_c3d7847a H hDraw
  exact ⟨J, hSub, hJDraw,
    WilliamsonShmoys.maximal_planar_edge_count_c3d7847a J hJDraw hCard hMax⟩