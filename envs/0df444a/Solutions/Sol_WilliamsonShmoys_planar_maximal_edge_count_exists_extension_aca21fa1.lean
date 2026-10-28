-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_exists_extension_aca21fa1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:49:36.440452+00:00
-- url     : https://prove2.me/submissions/c6c42c13-5bb7-4615-a1e0-dd1e14df2d7c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y) :
    Exists (fun Z : SimpleGraph V =>
      And (HasPlanarDrawingOn Z)
        (And ((u v : V) -> Y.Adj u v -> Z.Adj u v)
          ((W : SimpleGraph V) -> HasPlanarDrawingOn W ->
            ((u v : V) -> Z.Adj u v -> W.Adj u v) ->
            (u v : V) -> W.Adj u v -> Z.Adj u v))) := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => Y ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hY⟩⟩
  obtain ⟨hPQ, hQ⟩ : Y ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
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
