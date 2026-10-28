-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:07:35.64915+00:00
-- url     : https://prove2.me/submissions/e632c36a-e6e0-4c24-a034-b89a2499f62b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => R ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hRdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : R ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, hQ, fun G h1 hne h2 =>
    hne (congrArg SimpleGraph.edgeSet (key G (SimpleGraph.edgeSet_subset_edgeSet.mp h1) h2)).symm⟩
