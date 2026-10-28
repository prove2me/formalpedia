-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:24:55.261121+00:00
-- url     : https://prove2.me/submissions/e79538c2-ff56-4390-8b03-d314c4253acb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => L ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hL⟩⟩
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
    | exact ⟨hQ, hPQ, fun R h2 h1 => (key R h1 h2).le⟩
    | exact ⟨fun h => hPQ h, hQ, fun R h1 h2 => key R (fun _ _ h => h1 h) h2⟩
    | exact ⟨fun h => hPQ h, hQ, fun R h2 h1 => key R (fun _ _ h => h1 h) h2⟩⟩
