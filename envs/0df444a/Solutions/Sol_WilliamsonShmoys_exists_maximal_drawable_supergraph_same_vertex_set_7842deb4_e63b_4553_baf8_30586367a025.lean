-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:14:23.843704+00:00
-- url     : https://prove2.me/submissions/32d458d5-4ed1-4cb8-90d2-19681310b416

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) : ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧ (∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T ≤ S) := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => R ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hRdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : R ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
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
