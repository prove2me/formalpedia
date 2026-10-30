-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_augmentation_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:47:46.544182+00:00
-- url     : https://prove2.me/submissions/ae21c39f-d248-4c3f-8c6c-9dc2679ad812

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hMax⟩ :=
    WilliamsonShmoys.drawable_maximal_supergraph T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.maximal_drawable_edge_bound U hV hU hMax⟩