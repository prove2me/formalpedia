-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_edge_augmentation_finite_maximal_drawable_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:33:31.654948+00:00
-- url     : https://prove2.me/submissions/fec3c49f-15b5-4884-896f-3d715344fbce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
        ∀ Z : SimpleGraph V, Y < Z → ¬ WilliamsonShmoys.HasPlanarDrawingOn Z := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => X ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : X ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun Z hlt hZ => ?_⟩
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hlt.le, hZ⟩)
  omega
