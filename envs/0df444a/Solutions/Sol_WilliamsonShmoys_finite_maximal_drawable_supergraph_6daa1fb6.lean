-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_supergraph_6daa1fb6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:02:01.414874+00:00
-- url     : https://prove2.me/submissions/d50b59ab-78b6-41fb-9a93-b86b978541df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, HasPlanarDrawingOn Y ∧
      (∀ u v, X.Adj u v → Y.Adj u v) ∧
      ∀ Z : SimpleGraph V, HasPlanarDrawingOn Z →
        (∀ u v, Y.Adj u v → Z.Adj u v) → Z = Y := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => X ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hX⟩⟩
  obtain ⟨hPQ, hQ⟩ : X ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
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
