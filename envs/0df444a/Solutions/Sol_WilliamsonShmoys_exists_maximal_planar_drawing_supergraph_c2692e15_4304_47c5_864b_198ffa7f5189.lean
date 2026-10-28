-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:39:46.623073+00:00
-- url     : https://prove2.me/submissions/af4f8d24-45b6-4e1d-b630-04ff2b2b92d5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ Z : SimpleGraph V, W ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z ≤ W := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => U ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hU⟩⟩
  obtain ⟨hPQ, hQ⟩ : U ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  have hEq : R = Q := by
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact hEq.le
