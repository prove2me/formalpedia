-- Prove2me | solution 1 for WilliamsonShmoys.drawable_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:39:05.817519+00:00
-- url     : https://prove2.me/submissions/1e1b4a8a-f21a-46e4-b07f-5a72f5513d52

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ U := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => T ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨hPQ, hQ⟩ : T ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
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
    | exact ⟨hQ, hPQ, fun R h2 h1 => (key R h1 h2).le⟩
    | exact ⟨fun h => hPQ h, hQ, fun R h1 h2 => key R (fun _ _ h => h1 h) h2⟩
    | exact ⟨fun h => hPQ h, hQ, fun R h2 h1 => key R (fun _ _ h => h1 h) h2⟩⟩
