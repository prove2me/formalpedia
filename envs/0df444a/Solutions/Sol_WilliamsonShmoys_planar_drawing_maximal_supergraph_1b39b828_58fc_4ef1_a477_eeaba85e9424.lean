-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_1b39b828_58fc_4ef1_a477_eeaba85e9424
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:50:24.186373+00:00
-- url     : https://prove2.me/submissions/642e428b-1483-4896-b4fb-2dd04a617649

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hL⟩⟩
  obtain ⟨hPQ, hQ⟩ : L ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
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
