-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_maximal_for_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:40:06.484174+00:00
-- url     : https://prove2.me/submissions/e001aa1f-ebb9-4604-943d-e591b527bc5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet ⊆ Q.edgeSet ∧
      (∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R →
        Q.edgeSet ⊆ R.edgeSet → R.edgeSet ⊆ Q.edgeSet) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => P ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : P ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, SimpleGraph.edgeSet_mono hPQ, fun R hR hQR' => ?_⟩
  have hQR : Q ≤ R := SimpleGraph.edgeSet_subset_edgeSet.mp hQR'
  suffices R = Q by rw [this]
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
