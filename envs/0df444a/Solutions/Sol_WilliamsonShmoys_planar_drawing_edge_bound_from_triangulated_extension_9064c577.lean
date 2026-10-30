-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_from_triangulated_extension_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:37:19.24583+00:00
-- url     : https://prove2.me/submissions/91c076e9-bda3-4958-bc4a-b33bed48f30f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHDraw, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension K hDraw
  exact ⟨H, hKH, hHDraw,
    WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count H hHDraw hCard hMaximal⟩