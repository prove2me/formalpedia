-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists_v3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:10:25.567783+00:00
-- url     : https://prove2.me/submissions/98759a42-bed1-4b01-bad1-2f2b63c09ae0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ H' : SimpleGraph V,
        H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => K ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hK⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, hPQ, hQ, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _), key⟩
