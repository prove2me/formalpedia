-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_e5a7f9d6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:21:51.799052+00:00
-- url     : https://prove2.me/submissions/ed9c31b1-507b-4aad-afb6-aa43b3ec7f1b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧
        ∀ M : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hK⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, hPQ, fun R hR hQR => ?_⟩
  have hEq : R = Q := by
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact hEq.le
