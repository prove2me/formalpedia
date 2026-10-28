-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:20:23.364063+00:00
-- url     : https://prove2.me/submissions/66bbc833-69a0-4f82-ae9f-332fe33ed128

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => M ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hMdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : M ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
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
