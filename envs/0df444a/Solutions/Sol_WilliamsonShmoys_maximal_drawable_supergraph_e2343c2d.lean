-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_e2343c2d
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:03:49.755055+00:00
-- url     : https://prove2.me/submissions/1bdd1cfa-a0e0-4543-a482-24ece0236f62

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → K ≠ N → ¬ HasPlanarDrawingOn K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => M ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hM⟩⟩
  obtain ⟨hPQ, hQ⟩ : M ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  refine ⟨Q, hPQ, ?_, hQ, fun R h1 h2 h3 => h2 (key R h1 h3)⟩
  exact Set.ncard_le_ncard (fun e he => SimpleGraph.edgeSet_mono hPQ he) (Set.toFinite _)
