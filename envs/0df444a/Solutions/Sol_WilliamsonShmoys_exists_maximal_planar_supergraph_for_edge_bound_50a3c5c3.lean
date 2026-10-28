-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_50a3c5c3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:32:30.135999+00:00
-- url     : https://prove2.me/submissions/f2770712-e592-4eda-9e21-816bb8d2b184

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V,
        Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => P ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hPdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : P ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
  have key : ∀ Rx9 : SimpleGraph V, Qx9 ≤ Rx9 → WilliamsonShmoys.HasPlanarDrawingOn Rx9 → Rx9 = Qx9 := by
    intro Rx9 hQR hR
    by_contra hne
    have hlt : Qx9 < Rx9 := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax Rx9 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Qx9, by first
    | exact ⟨hPQ, hQ, fun Rx9 h1 h2 => key Rx9 h1 h2⟩
    | exact ⟨hPQ, hQ, fun Rx9 h1 h2 => (key Rx9 h1 h2).le⟩
    | exact ⟨hPQ, hQ, fun Rx9 h1 h2 => (key Rx9 h1 h2) ▸ le_rfl⟩
    | exact ⟨hQ, hPQ, fun Rx9 h2 h1 => key Rx9 h1 h2⟩
    | exact ⟨hQ, hPQ, fun Rx9 h2 h1 => (key Rx9 h1 h2).le⟩
    | exact ⟨fun h => hPQ h, hQ, fun Rx9 h1 h2 => key Rx9 (fun _ _ h => h1 h) h2⟩
    | exact ⟨fun h => hPQ h, hQ, fun Rx9 h2 h1 => key Rx9 (fun _ _ h => h1 h) h2⟩⟩
