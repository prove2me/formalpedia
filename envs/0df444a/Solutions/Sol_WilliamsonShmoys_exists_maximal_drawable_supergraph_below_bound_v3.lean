-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_below_bound_v3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:45:48.464879+00:00
-- url     : https://prove2.me/submissions/4cf6ed8b-632d-4250-a32f-a565b8e65200

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hNdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : N ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, by first
    | exact ⟨hPQ, hQ, fun R h1 h2 => key R h1 h2⟩
    | exact ⟨hPQ, hQ, fun R h1 h2 => (key R h1 h2).le⟩
    | exact ⟨hQ, hPQ, fun R h2 h1 => key R h1 h2⟩
    | exact ⟨hQ, hPQ, fun R h2 h1 => (key R h1 h2).le⟩⟩
