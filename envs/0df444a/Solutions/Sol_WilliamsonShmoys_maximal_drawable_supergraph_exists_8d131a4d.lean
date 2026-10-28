-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists_8d131a4d
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:25:46.674993+00:00
-- url     : https://prove2.me/submissions/36e4f8bc-f200-436d-882c-2d7b3ed5634e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      HasPlanarDrawingOn H ∧
      (N.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (∀ M : SimpleGraph V, H ≤ M → HasPlanarDrawingOn M → M ≤ H) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V =>
      N ≤ X0 ∧ HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hNQ, hQ⟩ : N ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hNQ, hQ, ?_, ?_⟩
  · exact_mod_cast Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hNQ) (Set.toFinite _)
  · intro M hQM hM
    by_contra hne
    have hlt : Q < M := lt_of_le_of_ne hQM (by rintro rfl; exact hne le_rfl)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNQ.trans hQM, hM⟩)
    omega
