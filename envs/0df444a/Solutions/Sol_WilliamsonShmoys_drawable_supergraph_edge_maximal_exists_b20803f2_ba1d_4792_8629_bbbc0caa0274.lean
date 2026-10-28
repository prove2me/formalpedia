-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:55:20.65648+00:00
-- url     : https://prove2.me/submissions/9762aadd-86ae-461d-bee4-33a3273c6e00

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_edge_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_subset_drawable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  apply WilliamsonShmoys.finite_edge_maximal_extension
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (hdown := ?_)
    J hDraw
  intro G H hGH hH
  exact WilliamsonShmoys.edge_subset_drawable hGH hH
