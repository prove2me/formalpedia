-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:22:18.608112+00:00
-- url     : https://prove2.me/submissions/80ec5346-6064-451e-9110-0a74601ff84e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNdraw : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      (∀ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K = M) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => N ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hNdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : N ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, SimpleGraph.edgeSet_mono hPQ, hQ, fun R hQR' hR => ?_⟩
  have hQR : Q ≤ R := SimpleGraph.edgeSet_subset_edgeSet.mp hQR'
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
