-- Prove2me | solution 1 for WilliamsonShmoys.drawable_planar_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:10:53.416647+00:00
-- url     : https://prove2.me/submissions/2cf4505a-04a9-4bd2-bfa3-ad8178b5d3e9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Z : SimpleGraph V, W ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ Y : SimpleGraph V, Z ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = Z := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => W ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hW⟩⟩
  obtain ⟨hPQ, hQ⟩ : W ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
